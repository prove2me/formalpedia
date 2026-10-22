-- Prove2me | solution 1 for RunwayCPS.DiscreteTime.remark_1
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T11:15:47.937502+00:00
-- url     : https://prove2.me/submissions/6546bd61-02c1-4ab9-99b5-a8f76f17f7dc

import Mathlib
import Definitions.Def_RunwayCPS_DiscreteTime_ModifiedNetwork

set_option autoImplicit false

open RunwayCPS.DiscreteTime

theorem solution {n : ℕ} [NeZero n] (I : Instance n) (hk : 1 ≤ I.k)
    (htri : TriangleIneq I.δ) (p : ℕ) (hp : 2 ≤ p) (i : List (Fin n))
    (hi : IsGNode I p i) :
    dmin I i = (I.δ (penult i) (RunwayCPS.Makespan.final i) : ℤ) ∧
      dmax I p i = (I.δ (penult i) (RunwayCPS.Makespan.final i) : ℤ) := by
  refine ⟨rfl, ?_⟩
  unfold dmax
  apply le_antisymm
  · rw [Finset.fold_max_le]
    refine ⟨le_rfl, fun c _ => ?_⟩
    have h := htri (penult i) (RunwayCPS.Makespan.final i) c
    have h' : (I.δ (penult i) c : ℤ) ≤ (I.δ (penult i) (RunwayCPS.Makespan.final i) : ℤ)
        + (I.δ (RunwayCPS.Makespan.final i) c : ℤ) := by exact_mod_cast h
    linarith
  · rw [Finset.le_fold_max]
    exact Or.inl (le_of_eq (by unfold dmin; rfl))
