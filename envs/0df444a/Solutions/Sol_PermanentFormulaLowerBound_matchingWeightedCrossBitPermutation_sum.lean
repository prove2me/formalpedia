-- Prove2me | solution 1 for PermanentFormulaLowerBound.matchingWeightedCrossBitPermutation_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:13.22648+00:00
-- url     : https://prove2.me/submissions/2c52a555-643c-495b-a461-4d72e8b8d81d

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentFormulaLowerBound_matchingCrossWeight_sum

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentFormulaLowerBound
universe u v w
open scoped BigOperators Kronecker Matrix IntermediateField.algebraAdjoinAdjoin
namespace PermanentFormulaLowerBound
theorem _root_.solution
    {F : Type*} [CommRing F] {ell m : ℕ}
    (p q : Fin m → F) (de ab : Fin m × Fin m) :
    (∑ σ : MatchingCrossPermutation
      (↥(matchingBitSubset ell (de.1 : ℕ)) ⊕
        ↥(matchingBitSubset ell (de.2 : ℕ)))
      {j : Fin m // j ≠ ab.1}
      {j : Fin m // j ≠ ab.2},
        matchingCrossWeight p q
          (matchingBitSubset ell (de.1 : ℕ))
          (matchingBitSubset ell (de.2 : ℕ)) ab.1 ab.2 σ) =
      matchingWeightedBivariateEvaluationMatrix p q
        (fun d : Fin m => matchingBitSubset ell (d : ℕ))
        (fun e : Fin m => matchingBitSubset ell (e : ℕ)) de ab := by
  exact matchingCrossWeight_sum p q
    (matchingBitSubset ell (de.1 : ℕ))
    (matchingBitSubset ell (de.2 : ℕ)) ab.1 ab.2
end PermanentFormulaLowerBound
