-- Prove2me | solution 1 for PvsNP.OnlineRegionRead.JointTrace.replays_hybrid
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-27T04:24:40.516454+00:00
-- url     : https://prove2.me/submissions/240445d8-325c-4524-8772-689f0b292b66

import Definitions.Def_OnlineRegionalTrace
set_option autoImplicit false

namespace PvsNP.OnlineRegionRead

open WorkBoundarySplice

variable {Q Γ : Type}

theorem merge_tick {M : Program Q Γ} {mask : ℤ → Bool} {owner : Bool} {word hybrid : Word}
    {a b : Cursor Q Γ} {scanned : Option ℕ}
    (here : mask a.work.head = owner) (event : tick M word a = some (b,scanned))
    (agree : ∀ i ∈ scanned.toList, word i = hybrid i) (outside : Cursor Q Γ) :
    tick M hybrid (merge mask owner a outside) = some (merge mask owner b outside,scanned) := by
  cases cmd : M a.work.state (a.work.tape a.work.head) with
  | localStep q value d =>
      simp only [tick,cmd,Option.some.injEq,Prod.mk.injEq] at event
      obtain ⟨rfl,rfl⟩ := event
      simp only [merge,tick,here,if_true,cmd,Option.some.injEq,Prod.mk.injEq,and_true,Cursor.mk.injEq,
        Config.mk.injEq,true_and]
      funext z
      by_cases same : z = a.work.head
      · subst z
        simp [write,here]
      · simp [write,same]
  | read next =>
      simp only [tick,cmd,Option.some.injEq,Prod.mk.injEq] at event
      obtain ⟨rfl,rfl⟩ := event
      have input := agree a.input (by simp)
      simp [merge,tick,here,cmd,input]
  | halt => simp [tick,cmd] at event

/-- Replace the inactive work cells and all input positions outside the
recorded reads, preserving every transition and read in the segment. -/
theorem Segment.replay {M : Program Q Γ} {mask : ℤ → Bool} {owner : Bool} {word hybrid : Word}
    {a b : Cursor Q Γ} {reads : List ℕ} {n : ℕ}
    (run : Segment M word mask owner a b reads n)
    (agree : ∀ i ∈ reads, word i = hybrid i) (outside : Cursor Q Γ) :
    Segment M hybrid mask owner (merge mask owner a outside) (merge mask owner b outside) reads n := by
  induction run with
  | refl => exact .refl _
  | next here first _ ih =>
      exact .next here (merge_tick here first (fun i hi => agree i (List.mem_append_left _ hi)) outside)
        (ih (fun i hi => agree i (List.mem_append_right _ hi)))

theorem tick_preserves_outside {M : Program Q Γ} {word : Word} {a b : Cursor Q Γ}
    {scanned : Option ℕ} (event : tick M word a = some (b,scanned))
    {z : ℤ} (different : z ≠ a.work.head) : b.work.tape z = a.work.tape z := by
  cases cmd : M a.work.state (a.work.tape a.work.head) with
  | localStep q value d =>
      simp only [tick,cmd,Option.some.injEq,Prod.mk.injEq] at event
      obtain ⟨rfl,rfl⟩ := event
      simp [write,different]
  | read next =>
      simp only [tick,cmd,Option.some.injEq,Prod.mk.injEq] at event
      obtain ⟨rfl,rfl⟩ := event
      rfl
  | halt => simp [tick,cmd] at event

theorem Segment.preserves_outside {M : Program Q Γ} {word : Word} {mask : ℤ → Bool}
    {owner : Bool} {a b : Cursor Q Γ} {reads : List ℕ} {n : ℕ}
    (run : Segment M word mask owner a b reads n) {z : ℤ} (outside : mask z ≠ owner) :
    b.work.tape z = a.work.tape z := by
  induction run with
  | refl => rfl
  | next here first _ ih =>
      have different : z ≠ _ := fun eq => outside (eq ▸ here)
      exact ih.trans (tick_preserves_outside first different)

theorem merge_comm {mask : ℤ → Bool} {a b : Cursor Q Γ} (same : Aligned a b) :
    merge mask true a b = merge mask false b a := by
  rcases a with ⟨⟨x,p,t⟩,i⟩
  rcases b with ⟨⟨y,q,u⟩,j⟩
  obtain ⟨rfl,rfl,rfl⟩ := same
  simp only [merge,Cursor.mk.injEq,Config.mk.injEq,true_and,and_true]
  funext z
  cases mask z <;> simp

theorem merge_change {before after : ℤ → Bool} {a b : Cursor Q Γ}
    (handed : ∀ z, before z ≠ after z → a.work.tape z = b.work.tape z) :
    merge before true a b = merge after true a b := by
  simp only [merge,Cursor.mk.injEq,Config.mk.injEq,true_and,and_true]
  funext z
  cases p : before z <;> cases q : after z <;> simp
  · exact (handed z (by simp [p,q])).symm
  · exact handed z (by simp [p,q])

theorem Run.append {M : Program Q Γ} {word : Word} {a b c : Cursor Q Γ} {n m : ℕ}
    (first : Run M word a b n) (rest : Run M word b c m) : Run M word a c (n+m) := by
  induction first with
  | refl => simpa using rest
  | next event _ ih => simpa [Nat.add_right_comm] using Run.next event (ih rest)

theorem Segment.toRun {M : Program Q Γ} {word : Word} {mask : ℤ → Bool}
    {owner : Bool} {a b : Cursor Q Γ} {reads : List ℕ} {n : ℕ}
    (run : Segment M word mask owner a b reads n) : Run M word a b n := by
  induction run with
  | refl => exact .refl _
  | next _ event _ ih => exact .next event ih

private theorem replace_inactive {mask : ℤ → Bool} {owner : Bool} {active old new : Cursor Q Γ}
    (frozen : ∀ z, mask z ≠ owner → new.work.tape z = old.work.tape z) :
    merge mask owner active old = merge mask owner active new := by
  simp only [merge,Cursor.mk.injEq,Config.mk.injEq,true_and,and_true]
  funext z
  by_cases owned : mask z = owner
  · simp [owned]
  · simp [owned,frozen z owned]

theorem splice_segment {M : Program Q Γ} {one zero : Word} {route : ℕ → Bool}
    {mask : ℤ → Bool} {owner : Bool} {a a' b b' : Cursor Q Γ}
    {readsA readsB : List ℕ} {n m : ℕ}
    (earlier : Aligned a b) (later : Aligned a' b')
    (left : Segment M one mask owner a a' readsA n)
    (right : Segment M zero mask owner b b' readsB m)
    (leftRoute : owner = true → ∀ i ∈ readsA, route i = true)
    (rightRoute : owner = false → ∀ i ∈ readsB, route i = false) :
    ∃ k, Run M (hybridWord route one zero) (merge mask true a b) (merge mask true a' b') k := by
  cases owner with
  | false =>
      rw [merge_comm earlier,merge_comm later]
      rw [← replace_inactive (active := b') (old := a) (new := a') (fun _ out => left.preserves_outside out)]
      refine ⟨m,(right.replay ?_ a).toRun⟩
      intro i hi
      simp [hybridWord,rightRoute rfl i hi]
  | true =>
      rw [← replace_inactive (active := a') (old := b) (new := b') (fun _ out => right.preserves_outside out)]
      refine ⟨n,(left.replay ?_ b).toRun⟩
      intro i hi
      simp [hybridWord,leftRoute rfl i hi]

/-- An input obtained by choosing either source at each recorded input
position has the corresponding hybrid run. The final control equals
the first source's final control. -/
theorem JointTrace.replay {M : Program Q Γ} {one zero : Word} {route : ℕ → Bool}
    {before after : ℤ → Bool} {a a' b b' : Cursor Q Γ}
    (trace : JointTrace M one zero route before a b after a' b') :
    ∃ k, Run M (hybridWord route one zero) (merge before true a b) (merge after true a' b') k := by
  induction trace with
  | refl => exact ⟨0,.refl _⟩
  | segment earlier later left right lr rr _ ih =>
      obtain ⟨n,front⟩ := splice_segment earlier later left right lr rr
      obtain ⟨m,back⟩ := ih
      exact ⟨n+m,front.append back⟩
  | handoff handed _ ih =>
      rw [merge_change handed]
      exact ih

end PvsNP.OnlineRegionRead

open PvsNP.OnlineRegionRead

theorem solution
    {Q Γ : Type} {M : Program Q Γ} {one zero : Word} {route : ℕ → Bool}
    {before after : ℤ → Bool} {a a' b b' : Cursor Q Γ}
    (trace : JointTrace M one zero route before a b after a' b') :
    ∃ k, Run M (hybridWord route one zero) (merge before true a b) (merge after true a' b') k := by
  exact trace.replay

#print axioms solution
