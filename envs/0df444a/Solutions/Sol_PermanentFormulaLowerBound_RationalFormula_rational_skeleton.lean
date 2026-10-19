-- Prove2me | solution 1 for PermanentFormulaLowerBound.RationalFormula.rational_skeleton
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:12.090475+00:00
-- url     : https://prove2.me/submissions/09144abb-7c11-4a35-ace2-563b213f3485

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentFormulaLowerBound_RationalFormula_exists_contractedRationalSkeleton

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentFormulaLowerBound
universe u v w
open scoped BigOperators Kronecker Matrix IntermediateField.algebraAdjoinAdjoin
open PermanentFormulaLowerBound.RationalFormula
noncomputable section
variable {Y Z F : Type*}
namespace PermanentFormulaLowerBound.RationalFormula
theorem _root_.solution [Field F]
    (f : RationalFormula (Y ⊕ Z) F) (hvalid : Valid f)
    (hmarked : 0 < yLeafCount f) :
    ∃ s : Finset (rationalCoefficientField Z F),
      s.card ≤ 6 * yLeafCount f - 3 ∧
        splitEval f ∈ rationalSkeletonField (Y := Y) s := by
  obtain ⟨w⟩ := exists_contractedRationalSkeleton f hvalid hmarked
  exact ⟨ContractedRationalSkeleton.extendedGenerators w,
    ContractedRationalSkeleton.extendedGenerators_card_le w hmarked,
    ContractedRationalSkeleton.splitEval_mem_extended w⟩
end PermanentFormulaLowerBound.RationalFormula
