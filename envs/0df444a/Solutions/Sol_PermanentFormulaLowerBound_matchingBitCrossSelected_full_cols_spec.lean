-- Prove2me | solution 1 for PermanentFormulaLowerBound.matchingBitCrossSelected_full_cols_spec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:13.22648+00:00
-- url     : https://prove2.me/submissions/78bf92a8-9401-4f03-a7e3-43a3e09d883f

import Mathlib
import Definitions.Def_Permanent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentFormulaLowerBound
universe u v w
open scoped BigOperators Kronecker Matrix IntermediateField.algebraAdjoinAdjoin
namespace PermanentFormulaLowerBound
theorem _root_.solution
    {ell m : ℕ} {de ab : Fin m × Fin m}
    (σ : MatchingBitCrossSelectedPermutation ell m de ab)
    (t : ↥(matchingBitSubset ell (de.1 : ℕ)) ⊕
      ↥(matchingBitSubset ell (de.2 : ℕ))) :
    σ.1.1
        (matchingBlockIndexEquiv ell m
          (.inr (matchingCrossCols
            (matchingBitCrossSelectedToCross σ) t).1)) =
      matchingBlockIndexEquiv ell m
        (.inl (matchingBitSurvivorEquiv ell m de t).1) := by
  have hcross :
      (matchingBitCrossSelectedToCross σ).1
        (.inr (matchingCrossCols
          (matchingBitCrossSelectedToCross σ) t)) = .inl t := by
    exact ((matchingBitCrossSelectedToCross σ).1.symm_apply_eq.mp
      (matchingCrossCols_spec
        (matchingBitCrossSelectedToCross σ) t)).symm
  exact
    (matchingBitCrossSelected_reduced_eq_iff σ
      (.inr (matchingCrossCols
        (matchingBitCrossSelectedToCross σ) t)) (.inl t)).mp hcross
end PermanentFormulaLowerBound
