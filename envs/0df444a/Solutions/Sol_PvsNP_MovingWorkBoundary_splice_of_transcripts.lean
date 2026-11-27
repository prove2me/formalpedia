-- Prove2me | solution 1 for PvsNP.MovingWorkBoundary.splice_of_transcripts
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-27T03:23:54.72725+00:00
-- url     : https://prove2.me/submissions/95410d0e-2934-457b-bda5-9c5b32ae50fe

import Definitions.Def_MovingWorkTapePartition

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
theorem _root_.solution (cut : ℕ → ℤ) (M : Machine Q Γ) (a b : Config Q Γ) (T : ℕ)
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

#print axioms solution
