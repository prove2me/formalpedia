-- Prove2me | solution 1 for PvsNP.WorkBoundarySplice.splice
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-27T03:04:59.22768+00:00
-- url     : https://prove2.me/submissions/726260f9-b250-48aa-a9de-284854abfac4

import Definitions.Def_SingleTapeWorkBoundary

set_option autoImplicit false

set_option maxHeartbeats 1000000

namespace PvsNP.WorkBoundarySplice

variable {Q Γ : Type*}

theorem patch_step {M : Machine Q Γ} {cut : ℤ} {s : Bool} {a b : Config Q Γ}
    (active : rightOf cut a.head = s) (run : step M a = some b)
    (other : Config Q Γ) :
    step M (patch cut s a other) = some (patch cut s b other) := by
  cases a with
  | mk q h tape =>
    change rightOf cut h = s at active
    cases command : M q (tape h) with
    | none => simp only [step,command,Option.map_none,reduceCtorEq] at run
    | some v =>
      rcases v with ⟨q',symbol,move⟩
      simp only [step,command,Option.map_some,Option.some.injEq] at run
      subst b
      simp only [step,patch,active,if_true,command,Option.map_some,Option.some.injEq,
        Config.mk.injEq,true_and]
      funext i
      by_cases hi : i = h
      · subst i
        simp only [write,if_true,active]
      · by_cases side : rightOf cut i = s <;> simp [write,hi,side]

theorem step_preserves_other_cell {M : Machine Q Γ} {a b : Config Q Γ}
    (run : step M a = some b) {cell : ℤ} (remote : cell ≠ a.head) :
    b.tape cell = a.tape cell := by
  unfold step at run
  cases command : M a.state (a.tape a.head) with
  | none => simp only [command,Option.map_none,reduceCtorEq] at run
  | some v =>
    rcases v with ⟨q,c,d⟩
    simp only [command,Option.map_some,Option.some.injEq] at run
    subst b
    exact if_neg remote

theorem step_unit {M : Machine Q Γ} {a b : Config Q Γ}
    (run : step M a = some b) : a.head-1 ≤ b.head ∧ b.head ≤ a.head+1 := by
  unfold step at run
  cases command : M a.state (a.tape a.head) with
  | none => simp only [command,Option.map_none,reduceCtorEq] at run
  | some v =>
    rcases v with ⟨q,c,d⟩
    simp only [command,Option.map_some,Option.some.injEq] at run
    subst b
    change a.head-1 ≤ d.shift a.head ∧ d.shift a.head ≤ a.head+1
    cases d <;> simp only [Motion.shift] <;> omega

theorem step_arrival_head {M : Machine Q Γ} {a b : Config Q Γ}
    (run : step M a = some b) (cut : ℤ)
    (cross : rightOf cut b.head ≠ rightOf cut a.head) :
    b.head = if rightOf cut a.head then cut else cut+1 := by
  have distance := step_unit run
  by_cases start : cut < a.head
  · have hs : rightOf cut a.head = true := decide_eq_true start
    have finish : ¬ cut < b.head := by
      intro hx
      exact cross ((decide_eq_true hx).trans hs.symm)
    rw [hs]
    change b.head = cut
    omega
  · have hs : rightOf cut a.head = false := decide_eq_false start
    have finish : cut < b.head := by
      by_contra hx
      exact cross ((decide_eq_false hx).trans hs.symm)
    rw [hs]
    change b.head = cut+1
    omega

namespace Stays

theorem side {M : Machine Q Γ} {cut : ℤ} {a b : Config Q Γ} {n : ℕ}
    (segment : Stays M cut a b n) : rightOf cut b.head = rightOf cut a.head := by
  induction segment with
  | refl => rfl
  | next _ eq _ ih => exact ih.trans eq

theorem unchanged {M : Machine Q Γ} {cut : ℤ} {a b : Config Q Γ} {n : ℕ}
    (segment : Stays M cut a b n) {i : ℤ} (remote : rightOf cut i ≠ rightOf cut a.head) :
    b.tape i = a.tape i := by
  induction segment with
  | refl => rfl
  | next h eq _ ih =>
    exact (ih (fun atB => remote (atB.trans eq))).trans
      (step_preserves_other_cell h (fun same => remote (congrArg (rightOf cut) same)))

theorem patched {M : Machine Q Γ} {cut : ℤ} {a b other : Config Q Γ} {n : ℕ}
    (segment : Stays M cut a b n) :
    Stays M cut (patch cut (rightOf cut a.head) a other)
      (patch cut (rightOf cut a.head) b other) n := by
  induction segment with
  | refl => exact .refl _
  | @next a b c n h eq _ ih =>
    refine .next (patch_step rfl h other) eq ?_
    rw [eq] at ih
    exact ih

end Stays

namespace Exits

theorem side {M : Machine Q Γ} {cut : ℤ} {a b : Config Q Γ} {n : ℕ}
    (exit : Exits M cut a b n) : rightOf cut b.head ≠ rightOf cut a.head := by
  obtain ⟨p,m,_,segment,_,h⟩ := exit
  exact fun same => h (same.trans segment.side.symm)

theorem arrival {M : Machine Q Γ} {cut : ℤ} {a b : Config Q Γ} {n : ℕ}
    (exit : Exits M cut a b n) :
    b.head = if rightOf cut a.head then cut else cut+1 := by
  obtain ⟨p,m,_,segment,last,h⟩ := exit
  exact (step_arrival_head last cut h).trans (congrArg (fun s => if s then cut else cut+1) segment.side)

theorem unchanged {M : Machine Q Γ} {cut : ℤ} {a b : Config Q Γ} {n : ℕ}
    (exit : Exits M cut a b n) {i : ℤ} (remote : rightOf cut i ≠ rightOf cut a.head) :
    b.tape i = a.tape i := by
  obtain ⟨p,m,_,segment,last,_⟩ := exit
  exact (step_preserves_other_cell last
    (fun same => remote ((congrArg (rightOf cut) same).trans segment.side))).trans
    (segment.unchanged remote)

theorem patched {M : Machine Q Γ} {cut : ℤ} {a b other : Config Q Γ} {n : ℕ}
    (exit : Exits M cut a b n) :
    Exits M cut (patch cut (rightOf cut a.head) a other)
      (patch cut (rightOf cut a.head) b other) n := by
  obtain ⟨p,m,eq,segment,last,h⟩ := exit
  exact ⟨patch cut (rightOf cut a.head) p other,m,eq,segment.patched,
    patch_step segment.side last other,h⟩

end Exits

private theorem switch_after_exits {M : Machine Q Γ} {cut : ℤ}
    {a b a' b' : Config Q Γ} {n m : ℕ} (ha : Exits M cut a a' n)
    (hb : Exits M cut b b' m) (sameHead : a.head = b.head) (sameState : a'.state = b'.state) :
    patch cut (rightOf cut a.head) a' b = patch cut (rightOf cut b'.head) b' a' := by
  have side0 := congrArg (rightOf cut) sameHead
  have side1 : rightOf cut b'.head ≠ rightOf cut a.head := fun hs => hb.side (hs.trans side0)
  have sameArrival : a'.head = b'.head :=
    ha.arrival.trans ((congrArg (fun s => if s then cut else cut+1) side0).trans hb.arrival.symm)
  have tapeEq : (patch cut (rightOf cut a.head) a' b).tape =
      (patch cut (rightOf cut b'.head) b' a').tape := by
    funext i
    by_cases hi : rightOf cut i = rightOf cut a.head
    · simp [patch,hi,side1.symm]
    · have hs : rightOf cut i = rightOf cut b'.head := by
        cases h : rightOf cut i <;> cases ha : rightOf cut a.head <;> cases hb : rightOf cut b'.head <;>
          simp_all
      have tape := hb.unchanged (i := i) (fun h => hi (h.trans side0.symm))
      simpa only [patch,if_neg hi,if_pos hs] using tape.symm

  dsimp only [patch] at tapeEq ⊢
  rw [sameState,sameArrival,tapeEq]

/-- Equal accepting work-boundary records permit splicing opposite initial
half-tapes. The result preserves the record and uses at most the sum of the
two runs' step counts. -/
theorem _root_.solution {M : Machine Q Γ} {cut : ℤ} {accept : Q → Prop}
    {record : List Q} {a b : Config Q Γ} {n m : ℕ}
    (sameHead : a.head = b.head)
    (left : Run M cut accept a record n) (right : Run M cut accept b record m) :
    ∃ k, k ≤ n+m ∧ Run M cut accept (patch cut (rightOf cut a.head) a b) record k := by
  induction record generalizing a b n m with
  | nil =>
    cases left with
    | finish stay accepts =>
      exact ⟨n,Nat.le_add_right _ _,.finish stay.patched accepts⟩
  | cons q record ih =>
    cases left with
    | @cross _ a' n₁ n₂ _ _ leftState leftExit leftRest =>
      cases right with
      | @cross _ b' m₁ m₂ _ _ rightState rightExit rightRest =>
        have obs : a'.state = b'.state := leftState.trans rightState.symm
        have arrival : b'.head = a'.head :=
          rightExit.arrival.trans (by rw [← sameHead,leftExit.arrival])
        obtain ⟨k,hk,rec⟩ := ih arrival rightRest leftRest
        have exchange := switch_after_exits leftExit rightExit sameHead obs
        have mixedExit := leftExit.patched (other := b)
        have mixedState : (patch cut (rightOf cut a.head) a' b).state = q := leftState
        refine ⟨n₁+k,by omega,.cross mixedState mixedExit ?_⟩
        rw [exchange]
        exact rec

end PvsNP.WorkBoundarySplice

#print axioms solution
