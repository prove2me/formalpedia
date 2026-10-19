-- Prove2me | solution 1 for PermanentRollout.permanent_rollout_homogeneous_linear_slice_ideal_snoc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:03.257302+00:00
-- url     : https://prove2.me/submissions/1f850bcb-8a17-4650-a643-cafe57f619bf

import Mathlib
import Definitions.Def_Permanent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open Set Filter Module
open scoped BigOperators ENNReal
noncomputable section
attribute [local instance] MvPolynomial.gradedAlgebra
namespace PermanentRollout
theorem _root_.solution
    {m n : ℕ} (I : Ideal (MvPolynomial (Fin m) ℂ))
    (c : Fin n → Fin m → ℂ) (x : Fin m → ℂ) :
    permanentRolloutHomogeneousLinearSliceIdeal I (Fin.snoc c x) =
      permanentRolloutHomogeneousLinearSliceIdeal I c ⊔
        Ideal.span
          ({permanentRolloutLinearCoordinateCombination m x} :
            Set (MvPolynomial (Fin m) ℂ)) := by
  unfold permanentRolloutHomogeneousLinearSliceIdeal
  have hsnoc :
      (fun j : Fin (n + 1) =>
        permanentRolloutLinearCoordinateCombination m
          ((Fin.snoc c x : Fin (n + 1) → Fin m → ℂ) j)) =
      Fin.snoc
        (fun j => permanentRolloutLinearCoordinateCombination m (c j))
        (permanentRolloutLinearCoordinateCombination m x) := by
    funext j
    induction j using Fin.lastCases <;> simp
  rw [hsnoc, Fin.range_snoc, Ideal.span_insert]
  ac_rfl
end PermanentRollout
