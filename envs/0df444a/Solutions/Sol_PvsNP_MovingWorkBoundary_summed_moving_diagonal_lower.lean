-- Prove2me | solution 1 for PvsNP.MovingWorkBoundary.summed_moving_diagonal_lower
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-27T03:36:28.72685+00:00
-- url     : https://prove2.me/submissions/65c5c38f-77d8-4457-b6c4-c1b59af602a0

import Definitions.Def_MovingCutCapacity

namespace PvsNP.WorkBoundarySplice

variable {Q Γ : Type}

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

end PvsNP.WorkBoundarySplice

set_option autoImplicit false

namespace PvsNP.MovingCutCharge

open PvsNP.WorkBoundarySplice

/-- A head can change sides only at one of the two old cut addresses
immediately at or before the new head, when both speeds are at most one. -/
theorem old_cut_at_head {cut cut' head head' : ℤ}
    (cutSpeed : cut-1 ≤ cut' ∧ cut' ≤ cut+1)
    (headSpeed : head-1 ≤ head' ∧ head' ≤ head+1)
    (flip : rightOf cut' head' ≠ rightOf cut head) :
    cut = head'-1 ∨ cut = head' := by
  by_cases old : cut < head
  · have oldSide : rightOf cut head = true := decide_eq_true old
    have new : ¬ cut' < head' := by
      intro h
      exact flip ((decide_eq_true h).trans oldSide.symm)
    omega
  · have oldSide : rightOf cut head = false := decide_eq_false old
    have new : cut' < head' := by
      by_contra h
      exact flip ((decide_eq_false h).trans oldSide.symm)
    omega

/-- Distinct unit-speed moving cuts can contribute at most two head-side
events per unit tape transition, even when the cuts move simultaneously. -/
theorem head_flips_le_two {E : Type} [Fintype E]
    (cut cut' : E → ℤ) (head head' : ℤ)
    (distinct : Function.Injective cut)
    (cutSpeed : ∀ e, cut e-1 ≤ cut' e ∧ cut' e ≤ cut e+1)
    (headSpeed : head-1 ≤ head' ∧ head' ≤ head+1) :
    (Finset.univ.filter fun e => rightOf (cut' e) head' ≠ rightOf (cut e) head).card ≤ 2 := by
  classical
  let cuts := Finset.univ.filter fun e => rightOf (cut' e) head' ≠ rightOf (cut e) head
  let possible : Finset ℤ := {head'-1,head'}
  have imageInside : cuts.image cut ⊆ possible := by
    intro x hx
    obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hx
    have flip := (Finset.mem_filter.mp he).2
    have loc := old_cut_at_head (cutSpeed e) headSpeed flip
    simpa [possible] using loc
  calc
    cuts.card = (cuts.image cut).card :=
      (Finset.card_image_of_injective cuts distinct).symm
    _ ≤ possible.card := Finset.card_le_card imageInside
    _ ≤ 2 := by
      have different : head'-1 ≠ head' := by omega
      simp [possible,different]

/-- The global control-message term for moving cuts remains linear in the
number of replay steps. It does not include the transferred tape symbols. -/
theorem head_flip_budget {E : Type} [Fintype E]
    (cuts : ℕ → E → ℤ) (head : ℕ → ℤ) (ticks : ℕ)
    (distinct : ∀ t < ticks, Function.Injective (cuts t))
    (cutSpeed : ∀ t < ticks, ∀ e, cuts t e-1 ≤ cuts (t+1) e ∧ cuts (t+1) e ≤ cuts t e+1)
    (headSpeed : ∀ t < ticks, head t-1 ≤ head (t+1) ∧ head (t+1) ≤ head t+1) :
    (∑ t ∈ Finset.range ticks,
      (Finset.univ.filter fun e => rightOf (cuts (t+1) e) (head (t+1)) ≠
        rightOf (cuts t e) (head t)).card) ≤ 2*ticks := by
  calc
    _ ≤ ∑ _t ∈ Finset.range ticks, 2 := by
      apply Finset.sum_le_sum
      intro t ht
      have ht' := Finset.mem_range.mp ht
      exact head_flips_le_two _ _ _ _ (distinct t ht') (cutSpeed t ht') (headSpeed t ht')
    _ = 2*ticks := by simp [Nat.mul_comm]

/-- Every one of arbitrarily many distinct moving cuts can transfer a
different cell in the same step, even though the stationary head stays on
the same side of all the cuts. -/
theorem one_step_handoffs_unbounded (k : ℕ) :
    ∃ (c c' cell : Fin k → ℤ), Function.Injective c ∧ Function.Injective c' ∧
      Function.Injective cell ∧
      ∀ e, c' e = c e+1 ∧
        rightOf (c e) (cell e) ≠ rightOf (c' e) (cell e) ∧
        rightOf (c e) (-1) = rightOf (c' e) (-1) := by
  refine ⟨fun e => (e.val : ℤ),fun e => (e.val : ℤ)+1,
    fun e => (e.val : ℤ)+1,?_,?_,?_,?_⟩
  · intro i j same
    change (i.val : ℤ) = (j.val : ℤ) at same
    exact Fin.ext (by omega)
  · intro i j same
    change (i.val : ℤ)+1 = (j.val : ℤ)+1 at same
    exact Fin.ext (by omega)
  · intro i j same
    change (i.val : ℤ)+1 = (j.val : ℤ)+1 at same
    exact Fin.ext (by omega)
  · intro e
    have near : (e.val : ℤ) < (e.val : ℤ)+1 := by omega
    have left : ¬ (e.val : ℤ) < -1 := by omega
    have left' : ¬ (e.val : ℤ)+1 < -1 := by omega
    simp [rightOf,near,left,left']

end PvsNP.MovingCutCharge

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace PvsNP.MovingWorkBoundary

open PvsNP.WorkBoundarySplice Function

variable {I Q Γ : Type}

private theorem step_preserves_other_cell {M : Machine Q Γ} {a b : Config Q Γ}
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

private theorem tick_remote (M : Machine Q Γ) (c : Config Q Γ) (i : ℤ) (remote : i ≠ c.head) :
    (tick M c).tape i = c.tape i := by
  unfold tick
  cases executed : step M c with
  | none => rfl
  | some _ => exact step_preserves_other_cell executed remote

private theorem tick_assemble_fixed (M : Machine Q Γ) (owner : ℤ → I)
    (active : I) (runs : I → Config Q Γ) (onSide : ∀ j, owner (runs j).head = active) :
    tick M (assemble owner active runs) = assemble owner active (fun j => tick M (runs j)) := by
  have read : (assemble owner active runs).tape (runs active).head =
      (runs active).tape (runs active).head := by
    change (runs (owner (runs active).head)).tape (runs active).head = _
    rw [onSide]
  have remote (i : ℤ) (elsewhere : owner i ≠ active) :
      (tick M (runs (owner i))).tape i = (runs (owner i)).tape i :=
    tick_remote M (runs (owner i)) i (fun same => elsewhere ((congrArg owner same).trans (onSide _)))
  cases command : M (runs active).state ((runs active).tape (runs active).head) with
  | none =>
    have unchanged : tick M (runs active) = runs active := by simp [tick,step,command]
    have assembled : tick M (assemble owner active runs) = assemble owner active runs := by
      change ((M (runs active).state
        ((assemble owner active runs).tape (runs active).head)).map _).getD _ = _
      rw [read,command]
      rfl
    rw [assembled]
    change Config.mk (runs active).state (runs active).head (fun i => (runs (owner i)).tape i) =
      Config.mk (tick M (runs active)).state (tick M (runs active)).head
        (fun i => (tick M (runs (owner i))).tape i)
    rw [unchanged]
    congr 1
    funext i
    by_cases belongs : owner i = active
    · rw [belongs,unchanged]
    · exact (remote i belongs).symm
  | some action =>
    obtain ⟨q,a,d⟩ := action
    have executed : tick M (runs active) =
        ⟨q,d.shift (runs active).head,write (runs active).tape (runs active).head a⟩ := by
      simp [tick,step,command]
    have assembled : tick M (assemble owner active runs) =
        ⟨q,d.shift (runs active).head,write (assemble owner active runs).tape (runs active).head a⟩ := by
      change ((M (runs active).state
        ((assemble owner active runs).tape (runs active).head)).map _).getD _ = _
      rw [read,command]
      rfl
    rw [assembled]
    change Config.mk q (d.shift (runs active).head)
        (write (assemble owner active runs).tape (runs active).head a) =
      Config.mk (tick M (runs active)).state (tick M (runs active)).head
        (fun i => (tick M (runs (owner i))).tape i)
    rw [executed]
    congr 1
    funext i
    by_cases belongs : owner i = active
    · rw [belongs,executed]
      by_cases atHead : i = (runs active).head
      · simp [write,atHead]
      · simp only [write,if_neg atHead]
        change (runs (owner i)).tape i = (runs active).tape i
        rw [belongs]
    · have away : i ≠ (runs active).head := fun eq => belongs ((congrArg owner eq).trans (onSide active))
      rw [remote i belongs,write,if_neg away]
      rfl

/-- Changing the partition preserves the assembled configuration when every
transferred cell has the same value in its two owners, and any transfer
of control preserves both the head address and control state. -/
theorem assemble_repartition (owner nextOwner : ℤ → I) (active nextActive : I)
    (runs : I → Config Q Γ)
    (handoff : ∀ i, owner i ≠ nextOwner i → (runs (owner i)).tape i = (runs (nextOwner i)).tape i)
    (control : active ≠ nextActive → (runs active).state = (runs nextActive).state ∧
      (runs active).head = (runs nextActive).head) :
    assemble owner active runs = assemble nextOwner nextActive runs := by
  have sameTape : (fun i => (runs (owner i)).tape i) = fun i => (runs (nextOwner i)).tape i := by
    funext i
    by_cases same : owner i = nextOwner i
    · rw [same]
    · exact handoff i same
  have sameHead : (runs active).state = (runs nextActive).state ∧
      (runs active).head = (runs nextActive).head := by
    by_cases same : active = nextActive
    · subst nextActive
      exact ⟨rfl,rfl⟩
    · exact control same
  unfold assemble
  rw [sameHead.1,sameHead.2,sameTape]

/-- These handoffs are necessary and sufficient to preserve exactly the
same assembled configuration across a repartition. -/
theorem assemble_repartition_iff (owner nextOwner : ℤ → I) (active nextActive : I)
    (runs : I → Config Q Γ) :
    assemble owner active runs = assemble nextOwner nextActive runs ↔
      (∀ i, owner i ≠ nextOwner i → (runs (owner i)).tape i = (runs (nextOwner i)).tape i) ∧
      (active ≠ nextActive → (runs active).state = (runs nextActive).state ∧
        (runs active).head = (runs nextActive).head) := by
  constructor
  · intro eq
    refine ⟨fun i _ => ?_,fun _ => ?_⟩
    · have cells := congrArg (fun c : Config Q Γ => c.tape i) eq
      exact cells
    · have state := congrArg Config.state eq
      have head := congrArg Config.head eq
      exact ⟨state,head⟩
  · rintro ⟨handoff,control⟩
    exact assemble_repartition owner nextOwner active nextActive runs handoff control

/-- Partition cells at each clock, step the active source, then hand off the
new cell owners and the new active control. Synchronizing precisely these
interfaces gives a valid execution for a moving work-tape partition. -/
theorem tick_splice (M : Machine Q Γ) (owner nextOwner : ℤ → I)
    (active nextActive : I) (runs : I → Config Q Γ)
    (onSide : ∀ j, owner (runs j).head = active)
    (handoff : ∀ i, owner i ≠ nextOwner i →
      (tick M (runs (owner i))).tape i = (tick M (runs (nextOwner i))).tape i)
    (control : active ≠ nextActive →
      (tick M (runs active)).state = (tick M (runs nextActive)).state ∧
      (tick M (runs active)).head = (tick M (runs nextActive)).head) :
    tick M (assemble owner active runs) =
      assemble nextOwner nextActive (fun j => tick M (runs j)) := by
  rw [tick_assemble_fixed M owner active runs onSide]
  exact assemble_repartition owner nextOwner active nextActive _ handoff control

/-- Exact finite-clock splicing along an arbitrary sequence of partitions.
The boundary schedule is shared and source traces are synchronized. -/
theorem iterate_splice (M : Machine Q Γ) (owner : ℕ → ℤ → I) (active : ℕ → I)
    (runs : I → Config Q Γ) (T : ℕ)
    (onSide : ∀ t < T, ∀ j, owner t ((tick M)^[t] (runs j)).head = active t)
    (handoff : ∀ t < T, ∀ i, owner t i ≠ owner (t+1) i →
      ((tick M)^[t+1] (runs (owner t i))).tape i = ((tick M)^[t+1] (runs (owner (t+1) i))).tape i)
    (control : ∀ t < T, active t ≠ active (t+1) →
      ((tick M)^[t+1] (runs (active t))).state = ((tick M)^[t+1] (runs (active (t+1)))).state ∧
      ((tick M)^[t+1] (runs (active t))).head = ((tick M)^[t+1] (runs (active (t+1)))).head) :
    (tick M)^[T] (assemble (owner 0) (active 0) runs) =
      assemble (owner T) (active T) (fun j => (tick M)^[T] (runs j)) := by
  have equal (t : ℕ) (before : t ≤ T) :
      (tick M)^[t] (assemble (owner 0) (active 0) runs) =
        assemble (owner t) (active t) (fun j => (tick M)^[t] (runs j)) := by
    induction t with
    | zero => rfl
    | succ t ih =>
      have earlier : t < T := before
      rw [iterate_succ_apply',ih (Nat.le_of_lt earlier)]
      have changeOwner := tick_splice M (owner t) (owner (t+1)) (active t) (active (t+1))
        (fun j => (tick M)^[t] (runs j)) (onSide t earlier)
        (by simpa only [iterate_succ_apply'] using handoff t earlier)
        (by simpa only [iterate_succ_apply'] using control t earlier)
      simpa only [iterate_succ_apply'] using changeOwner
  exact equal T le_rfl

private theorem next_side_eq {cut : ℕ → ℤ} {M : Machine Q Γ} {a b : Config Q Γ} {t : ℕ}
    (initial : sideAt cut M a t = sideAt cut M b t)
    (event : controlAt cut M a t = controlAt cut M b t) :
    sideAt cut M a (t+1) = sideAt cut M b (t+1) := by
  have status : (controlAt cut M a t).isSome = (controlAt cut M b t).isSome :=
    congrArg Option.isSome event
  by_cases first : sideAt cut M a t = sideAt cut M a (t+1) <;>
    by_cases second : sideAt cut M b t = sideAt cut M b (t+1)
  · exact first.symm.trans (initial.trans second)
  · simp [controlAt,first,second] at status
  · simp [controlAt,first,second] at status
  · have flipA : sideAt cut M a (t+1) = !(sideAt cut M a t) := by
      cases h : sideAt cut M a t <;> simp_all
    have flipB : sideAt cut M b (t+1) = !(sideAt cut M b t) := by
      cases h : sideAt cut M b t <;> simp_all
    rw [flipA,flipB,initial]

private theorem control_equal_on_flip {cut : ℕ → ℤ} {M : Machine Q Γ} {a b : Config Q Γ} {t : ℕ}
    (before : sideAt cut M a t = sideAt cut M b t)
    (after : sideAt cut M a (t+1) = sideAt cut M b (t+1))
    (flip : sideAt cut M a t ≠ sideAt cut M a (t+1))
    (event : controlAt cut M a t = controlAt cut M b t) :
    (trace M a (t+1)).state = (trace M b (t+1)).state ∧
      (trace M a (t+1)).head = (trace M b (t+1)).head := by
  have other : sideAt cut M b t ≠ sideAt cut M b (t+1) := by simpa only [← before,← after] using flip
  rw [controlAt,controlAt,if_neg flip,if_neg other] at event
  exact Prod.mk.inj (Option.some.inj event)

/-- Equal moving-cut transcripts splice two computations at the same clock.
The cut path is fixed for both computations. It may change at every step. -/
theorem splice_of_transcripts (cut : ℕ → ℤ) (M : Machine Q Γ) (a b : Config Q Γ) (T : ℕ)
    (initial : sideAt cut M a 0 = sideAt cut M b 0)
    (controls : ∀ t < T, controlAt cut M a t = controlAt cut M b t)
    (handoffs : ∀ t < T, ∀ i, cellAt cut M a t i = cellAt cut M b t i) :
    trace M (assemble (rightOf (cut 0)) (sideAt cut M a 0) (pair a b)) T =
      assemble (rightOf (cut T)) (sideAt cut M a T)
        (fun side => trace M (pair a b side) T) := by
  have same (t : ℕ) (within : t ≤ T) : sideAt cut M a t = sideAt cut M b t := by
    induction t with
    | zero => exact initial
    | succ t ih =>
      have before : t < T := within
      exact next_side_eq (ih (Nat.le_of_lt before)) (controls t before)
  apply iterate_splice M (fun t => rightOf (cut t)) (sideAt cut M a) (pair a b) T
  · intro t before j
    cases j
    · rfl
    · exact (same t (Nat.le_of_lt before)).symm
  · intro t before i moved
    have agree := handoffs t before i
    rw [cellAt,cellAt,if_neg moved,if_neg moved] at agree
    have exactAgree := Option.some.inj agree
    change (trace M (pair a b (rightOf (cut t) i)) (t+1)).tape i =
      (trace M (pair a b (rightOf (cut (t+1)) i)) (t+1)).tape i
    cases p : rightOf (cut t) i <;> cases q : rightOf (cut (t+1)) i
    · rfl
    · exact exactAgree
    · exact exactAgree.symm
    · rfl
  · intro t before flip
    have agree := control_equal_on_flip (same t (Nat.le_of_lt before))
      (same (t+1) before) flip (controls t before)
    cases p : sideAt cut M a t <;> cases q : sideAt cut M a (t+1)
    · exact ⟨rfl,rfl⟩
    · exact agree
    · exact ⟨agree.1.symm,agree.2.symm⟩
    · exact ⟨rfl,rfl⟩

end PvsNP.MovingWorkBoundary

namespace PvsNP.MovingWorkBoundary

open PvsNP.WorkBoundarySplice

variable {Q Γ : Type}

/-- A common verdict at the fixed horizon survives the mixed computation. -/
theorem verdict_of_transcripts (cut : ℕ → ℤ) (M : Machine Q Γ) (a b : Config Q Γ) (T : ℕ)
    (verdict : Q → Prop)
    (initial : sideAt cut M a 0 = sideAt cut M b 0)
    (controls : ∀ t < T, controlAt cut M a t = controlAt cut M b t)
    (handoffs : ∀ t < T, ∀ i, cellAt cut M a t i = cellAt cut M b t i)
    (left : verdict (trace M a T).state) (right : verdict (trace M b T).state) :
    verdict (trace M (assemble (rightOf (cut 0)) (sideAt cut M a 0) (pair a b)) T).state := by
  rw [splice_of_transcripts cut M a b T initial controls handoffs]
  change verdict (trace M (pair a b (sideAt cut M a T)) T).state
  cases sideAt cut M a T
  · exact left
  · exact right

end PvsNP.MovingWorkBoundary

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace PvsNP.MovingWorkBoundary

open PvsNP.WorkBoundarySplice PvsNP.MovingCutCharge Function

variable {Q Γ : Type}

theorem trace_step (M : Machine Q Γ) (a : Config Q Γ) (t : ℕ) :
    trace M a (t+1) = tick M (trace M a t) := iterate_succ_apply' ..

theorem trace_head_unit (M : Machine Q Γ) (a : Config Q Γ) (t : ℕ) :
    (trace M a t).head-1 ≤ (trace M a (t+1)).head ∧
      (trace M a (t+1)).head ≤ (trace M a t).head+1 := by
  rw [trace_step]
  unfold tick
  cases ran : step M (trace M a t) with
  | none =>
    change (trace M a t).head-1 ≤ (trace M a t).head ∧
      (trace M a t).head ≤ (trace M a t).head+1
    omega
  | some _ => exact step_unit ran

private theorem control_head_range {cut : ℕ → ℤ} {M : Machine Q Γ} {a : Config Q Γ}
    {t : ℕ} {q : Q} {h : ℤ} (unit : cut t-1 ≤ cut (t+1) ∧ cut (t+1) ≤ cut t+1)
    (event : controlAt cut M a t = some (q,h)) :
    cut (t+1)-1 ≤ h ∧ h ≤ cut (t+1)+2 := by
  unfold controlAt at event
  split at event
  · contradiction
  · rename_i flip
    have located := old_cut_at_head unit (trace_head_unit M a t)
      (show rightOf (cut (t+1)) (trace M a (t+1)).head ≠ rightOf (cut t) (trace M a t).head from Ne.symm flip)
    have head := (Prod.mk.inj (Option.some.inj event)).2
    rw [head] at located
    omega

private theorem headOffset_inj {cut h h' : ℤ}
    (near : cut-1 ≤ h ∧ h ≤ cut+2) (near' : cut-1 ≤ h' ∧ h' ≤ cut+2)
    (same : headOffset cut h = headOffset cut h') : h = h' := by
  have eq := congrArg Fin.val same
  change (h-cut+1).toNat%4 = (h'-cut+1).toNat%4 at eq
  rw [Nat.mod_eq_of_lt (by omega),Nat.mod_eq_of_lt (by omega)] at eq
  omega

theorem controlCode_correct {cut : ℕ → ℤ} {M : Machine Q Γ} {a b : Config Q Γ} {t : ℕ}
    (unit : cut t-1 ≤ cut (t+1) ∧ cut (t+1) ≤ cut t+1)
    (same : controlCode cut M a t = controlCode cut M b t) :
    controlAt cut M a t = controlAt cut M b t := by
  unfold controlCode at same
  cases aCode : controlAt cut M a t with
  | none =>
    rw [aCode,Option.map_none] at same
    exact (Option.map_eq_none_iff.mp same.symm).symm
  | some p =>
    obtain ⟨q,h⟩ := p
    cases bCode : controlAt cut M b t with
    | none => simp [aCode,bCode] at same
    | some p' =>
      obtain ⟨q',h'⟩ := p'
      simp only [aCode,bCode,Option.map_some,Option.some.injEq,Prod.mk.injEq] at same
      have pos := headOffset_inj (control_head_range unit aCode) (control_head_range unit bCode) same.2
      rw [same.1,pos]

private theorem rightOf_congr {x y i : ℤ} (equivalence : x < i ↔ y < i) :
    rightOf x i = rightOf y i := by
  by_cases hit : x < i
  · exact (decide_eq_true hit).trans (decide_eq_true (equivalence.mp hit)).symm
  · have miss : ¬ y < i := fun h => hit (equivalence.mpr h)
    exact (decide_eq_false hit).trans (decide_eq_false miss).symm

private theorem handoff_at_max {x y i : ℤ} (unit : x-1 ≤ y ∧ y ≤ x+1)
    (handoff : rightOf x i ≠ rightOf y i) : x ≠ y ∧ i = max x y := by
  have distinct : x ≠ y := fun eq => handoff (congrArg (fun q => rightOf q i) eq)
  refine ⟨distinct,?_⟩
  rcases lt_or_gt_of_ne distinct with less|greater
  · rw [max_eq_right less.le]
    by_contra notEqual
    have equivalence : x < i ↔ y < i := by omega
    exact handoff (rightOf_congr equivalence)
  · rw [max_eq_left greater.le]
    by_contra notEqual
    have equivalence : x < i ↔ y < i := by omega
    exact handoff (rightOf_congr equivalence)

theorem handoffCode_correct {cut : ℕ → ℤ} {M : Machine Q Γ} {a b : Config Q Γ} {T : ℕ}
    (unit : UnitCut cut T) (same : handoffCode cut M a T = handoffCode cut M b T) :
    ∀ t < T, ∀ i, cellAt cut M a t i = cellAt cut M b t i := by
  intro t room i
  unfold cellAt
  by_cases stable : rightOf (cut t) i = rightOf (cut (t+1)) i
  · rw [if_pos stable,if_pos stable]
  · obtain ⟨moved,loc⟩ := handoff_at_max (unit t room) stable
    rw [if_neg stable,if_neg stable,loc]
    have label := congrFun same ⟨⟨t,room⟩,moved⟩
    exact congrArg some label

private theorem mem_timedEvents (cut : ℕ → ℤ) (M : Machine Q Γ) (a : Config Q Γ)
    {T : ℕ} (t : Fin T) (q : Q × Fin 4) :
    (t,q) ∈ timedEvents cut M a T ↔ controlCode cut M a t.val = some q := by
  rw [timedEvents,List.mem_filterMap]
  constructor
  · rintro ⟨s,_,hit⟩
    obtain ⟨v,labeled,equal⟩ := Option.map_eq_some_iff.mp hit
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj equal
    exact labeled
  · intro hit
    exact ⟨t,by simp,by simp [hit]⟩

theorem timedEvents_correct {cut : ℕ → ℤ} {M : Machine Q Γ} {a b : Config Q Γ}
    {T : ℕ} (unit : UnitCut cut T) (same : timedEvents cut M a T = timedEvents cut M b T) :
    ∀ t < T, controlAt cut M a t = controlAt cut M b t := by
  intro n room
  apply controlCode_correct (unit n room)
  let t : Fin T := ⟨n,room⟩
  change controlCode cut M a t.val = controlCode cut M b t.val
  cases asCode : controlCode cut M a t.val with
  | none =>
    cases bsCode : controlCode cut M b t.val with
    | none => rfl
    | some q =>
      have member := (mem_timedEvents cut M b t q).mpr bsCode
      rw [← same] at member
      have impossible := (mem_timedEvents cut M a t q).mp member
      rw [asCode] at impossible
      contradiction
  | some q =>
    have member := (mem_timedEvents cut M a t q).mpr asCode
    rw [same] at member
    exact ((mem_timedEvents cut M b t q).mp member).symm

theorem signature_correct {cut : ℕ → ℤ} {M : Machine Q Γ}
    {a b : Config Q Γ} {T r : ℕ} (unit : UnitCut cut T)
    (shortA : (timedEvents cut M a T).length ≤ r) (shortB : (timedEvents cut M b T).length ≤ r)
    (same : signature cut M a T r = signature cut M b T r) :
    sideAt cut M a 0 = sideAt cut M b 0 ∧
      (∀ t < T, controlAt cut M a t = controlAt cut M b t) ∧
      (∀ t < T, ∀ i, cellAt cut M a t i = cellAt cut M b t i) := by
  have initial := congrArg Prod.fst same
  have codes := congrArg (fun v : Signature cut T r Q Γ => v.2.1) same
  have cells := congrArg (fun v : Signature cut T r Q Γ => v.2.2) same
  refine ⟨initial,timedEvents_correct unit ?_,handoffCode_correct unit cells⟩
  apply List.ext_getElem?
  intro n
  by_cases within : n < r
  · exact congrFun codes ⟨n,within⟩
  · rw [List.getElem?_eq_none (by omega),List.getElem?_eq_none (by omega)]

theorem signature_card {Q Γ : Type} [Fintype Q] [Fintype Γ]
    (cut : ℕ → ℤ) (T r : ℕ) :
    Fintype.card (Signature cut T r Q Γ) =
      2*(T*(Fintype.card Q*4)+1)^r*(Fintype.card Γ)^(Fintype.card (MoveTime cut T)) := by
  simp only [Signature,TimedEvent,Fintype.card_prod,Fintype.card_bool,Fintype.card_fun,
    Fintype.card_fin,Fintype.card_option]
  ring

end PvsNP.MovingWorkBoundary

set_option autoImplicit false
set_option maxHeartbeats 1500000

namespace PvsNP.MovingWorkBoundary

open PvsNP.WorkBoundarySplice

variable {A Q Γ : Type} [Fintype A] [Fintype Q] [Fintype Γ]

/-- The moving-cut signature must encode every diagonal whose mixed input
changes the verdict. Each boundary move contributes one public-address
tape symbol in addition to the bounded time-stamped control messages. -/
theorem moving_diagonal_capacity (cut : ℕ → ℤ) (M : Machine Q Γ) (T r : ℕ)
    (unit : UnitCut cut T) (start : A → A → Config Q Γ) (verdict : Q → Prop)
    (mixed : ∀ a b,
      assemble (rightOf (cut 0)) (sideAt cut M (start a a) 0) (pair (start a a) (start b b)) = start a b)
    (diagonal : ∀ a, verdict (trace M (start a a) T).state)
    (offDiagonal : ∀ a b, a ≠ b → ¬ verdict (trace M (start a b) T).state)
    (short : ∀ a, (timedEvents cut M (start a a) T).length ≤ r) :
    Fintype.card A ≤
      2*(T*(Fintype.card Q*4)+1)^r*(Fintype.card Γ)^(Fintype.card (MoveTime cut T)) := by
  let code : A → Signature cut T r Q Γ := fun a => signature cut M (start a a) T r
  have unique : Function.Injective code := by
    intro a b hit
    by_contra different
    obtain ⟨initial,controls,handoffs⟩ := signature_correct unit (short a) (short b) hit
    have verdictMixed := verdict_of_transcripts cut M (start a a) (start b b) T verdict
      initial controls handoffs (diagonal a) (diagonal b)
    rw [mixed] at verdictMixed
    exact offDiagonal a b different verdictMixed
  rw [← signature_card (Q := Q) (Γ := Γ) cut T r]
  exact Fintype.card_le_of_injective code unique

end PvsNP.MovingWorkBoundary

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace PvsNP.MovingWorkBoundary

open PvsNP.WorkBoundarySplice PvsNP.MovingCutCharge
open scoped BigOperators

variable {A Q Γ : Type}

theorem timedEvents_card (cut : ℕ → ℤ) (M : Machine Q Γ) (a : Config Q Γ) (T : ℕ) :
    (timedEvents cut M a T).length =
    ((Finset.univ : Finset (Fin T)).filter (fun t =>
      sideAt cut M a t.val ≠ sideAt cut M a (t.val+1))).card := by
  classical
  let p : Fin T → Bool := fun t =>
    decide (sideAt cut M a t.val ≠ sideAt cut M a (t.val+1))
  have lengths : (timedEvents cut M a T).length = ((List.finRange T).filter p).length := by
    rw [timedEvents,List.length_filterMap_eq_countP,List.countP_eq_length_filter]
    have samePred : (fun t : Fin T => ((controlCode cut M a t.val).map (fun q => (t,q))).isSome) = p := by
      funext t
      dsimp only [controlCode,p]
      by_cases stayed : sideAt cut M a t.val = sideAt cut M a (t.val+1) <;>
        simp [controlAt,stayed]
    rw [samePred]
  rw [lengths,← List.toFinset_card_of_nodup ((List.nodup_finRange T).filter p),List.toFinset_filter]
  have full : (List.finRange T).toFinset = (Finset.univ : Finset (Fin T)) := by
    ext t
    simp
  simp [full,p]

theorem summed_control_budget {E : Type} [Fintype E] (cut : E → ℕ → ℤ)
    (M : Machine Q Γ) (a : Config Q Γ) (T : ℕ)
    (distinct : ∀ t < T, Function.Injective (fun e => cut e t))
    (speed : ∀ e, UnitCut (cut e) T) :
    ∑ e, (timedEvents (cut e) M a T).length ≤ 2*T := by
  classical
  let flip : E → Fin T → Prop := fun e t =>
    sideAt (cut e) M a t.val ≠ sideAt (cut e) M a (t.val+1)
  let f : E → Fin T → ℕ := fun e t => if flip e t then 1 else 0
  have sumCut (e : E) : (timedEvents (cut e) M a T).length = ∑ t : Fin T, f e t := by
    rw [timedEvents_card]
    exact Finset.card_filter (flip e) Finset.univ
  calc
    _ = ∑ e : E, ∑ t : Fin T, f e t :=
      Finset.sum_congr rfl (fun e _ => sumCut e)
    _ = ∑ t : Fin T, ∑ e : E, f e t := Finset.sum_comm
    _ ≤ ∑ _t : Fin T, 2 := by
      apply Finset.sum_le_sum
      intro t _
      change (∑ e : E, if flip e t then 1 else 0) ≤ 2
      rw [← Finset.card_filter (fun e => flip e t) Finset.univ]
      have budget := head_flips_le_two (fun e => cut e t.val) (fun e => cut e (t.val+1))
        (trace M a t.val).head (trace M a (t.val+1)).head
        (distinct t.val t.isLt) (fun e => speed e t.val t.isLt) (trace_head_unit M a t.val)
      let changed := (Finset.univ : Finset E).filter (fun e =>
        rightOf (cut e (t.val+1)) (trace M a (t.val+1)).head ≠
          rightOf (cut e t.val) (trace M a t.val).head)
      have exactBudget : changed.card ≤ 2 := budget
      have subset : ((Finset.univ : Finset E).filter (fun e => flip e t)) ⊆ changed := by
        intro e member
        have switched : flip e t := (Finset.mem_filter.mp member).2
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,Ne.symm switched⟩
      exact (Finset.card_le_card subset).trans exactBudget
    _ = 2*T := by simp [Nat.mul_comm]

variable [Fintype A] [Fintype Q] [Fintype Γ]

private theorem one_cut_control_sum (cut : ℕ → ℤ) (M : Machine Q Γ) (T r : ℕ)
    (unit : UnitCut cut T) (start : A → A → Config Q Γ) (verdict : Q → Prop)
    (mixed : ∀ a b,
      assemble (rightOf (cut 0)) (sideAt cut M (start a a) 0) (pair (start a a) (start b b)) = start a b)
    (diagonal : ∀ a, verdict (trace M (start a a) T).state)
    (offDiagonal : ∀ a b, a ≠ b → ¬ verdict (trace M (start a b) T).state) :
    (Fintype.card A - cutCapacity cut T r Q Γ)*(r+1) ≤
      ∑ a : A, (timedEvents cut M (start a a) T).length := by
  classical
  let count (a : A) := (timedEvents cut M (start a a) T).length
  let short := Finset.univ.filter (fun a => count a ≤ r)
  let long := Finset.univ.filter (fun a => r < count a)
  have shortCap : short.card ≤ cutCapacity cut T r Q Γ := by
    have cap := moving_diagonal_capacity cut M T r unit
      (fun a b : ↥short => start a.val b.val) verdict
      (fun a b => mixed a.val b.val) (fun a => diagonal a.val)
      (fun a b h => offDiagonal a.val b.val (fun eq => h (Subtype.ext eq)))
      (fun a => (Finset.mem_filter.mp a.property).2)
    simpa only [Fintype.card_coe, cutCapacity] using cap
  have split : short.card + long.card = Fintype.card A := by
    have partition := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset A)) (p := fun a => count a ≤ r)
    simpa only [short,long,not_le,Finset.card_univ] using partition
  have remaining : Fintype.card A-cutCapacity cut T r Q Γ ≤ long.card := by omega
  calc
    _ ≤ long.card*(r+1) := Nat.mul_le_mul_right _ remaining
    _ = ∑ _a ∈ long, (r+1) := by simp
    _ ≤ ∑ a ∈ long, count a :=
      by
        apply Finset.sum_le_sum
        intro a member
        change a ∈ Finset.univ.filter (fun a => r < count a) at member
        exact Nat.succ_le_of_lt (Finset.mem_filter.mp member).2
    _ ≤ ∑ a : A, count a := Finset.sum_le_sum_of_subset (Finset.subset_univ _)

/-- A common changing-cut partition can force many control transfers only
after its tape-handoff term is included in the per-cut signature capacity. -/
theorem _root_.solution {E : Type} [Fintype E] (cut : E → ℕ → ℤ)
    (M : Machine Q Γ) (T r : ℕ) (speed : ∀ e, UnitCut (cut e) T)
    (distinct : ∀ t < T, Function.Injective (fun e => cut e t))
    (start : A → A → Config Q Γ) (verdict : Q → Prop)
    (mixed : ∀ e a b,
      assemble (rightOf (cut e 0)) (sideAt (cut e) M (start a a) 0) (pair (start a a) (start b b)) = start a b)
    (diagonal : ∀ a, verdict (trace M (start a a) T).state)
    (offDiagonal : ∀ a b, a ≠ b → ¬ verdict (trace M (start a b) T).state) :
    (∑ e : E, (Fintype.card A - cutCapacity (cut e) T r Q Γ)*(r+1)) ≤
      Fintype.card A*(2*T) := by
  classical
  calc
    _ ≤ ∑ e : E, ∑ a : A, (timedEvents (cut e) M (start a a) T).length :=
      Finset.sum_le_sum (fun e _ => one_cut_control_sum (cut e) M T r (speed e) start verdict
        (mixed e) diagonal offDiagonal)
    _ = ∑ a : A, ∑ e : E, (timedEvents (cut e) M (start a a) T).length := Finset.sum_comm
    _ ≤ ∑ _a : A, 2*T := Finset.sum_le_sum (fun a _ => summed_control_budget cut M (start a a) T distinct speed)
    _ = _ := by simp

end PvsNP.MovingWorkBoundary

#print axioms solution
