-- Prove2me | solution 1 for PermanentFormulaLowerBound.Formula.contractedSkeletonRootGenerators_card_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:13.22648+00:00
-- url     : https://prove2.me/submissions/d4854ffa-644f-44c7-b213-11ae228e951c

import Mathlib
import Definitions.Def_Permanent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentFormulaLowerBound
universe u v w
open scoped BigOperators Kronecker Matrix IntermediateField.algebraAdjoinAdjoin
open PermanentFormulaLowerBound.Formula
variable {Y : Type u} {Z : Type v} {F : Type w}
variable [Field F]
namespace PermanentFormulaLowerBound.Formula
theorem _root_.solution
    {f : Formula (Y ⊕ Z) F}
    (w : ContractedSkeleton f) (hmarked : 0 < yLeafCount f) :
    (contractedSkeletonRootGenerators w).card ≤
      4 * yLeafCount f - 2 := by
  classical
  have hroot : (contractedSkeletonRootExtras w).card ≤ 2 := by
    unfold contractedSkeletonRootExtras
    exact Finset.card_le_two
  have hunion := Finset.card_union_le
    (contractedSkeletonRootExtras w) w.generators
  have hinternal := w.generator_card
  change ((contractedSkeletonRootExtras w) ∪ w.generators).card ≤
    4 * yLeafCount f - 2
  omega
end PermanentFormulaLowerBound.Formula
