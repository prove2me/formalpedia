-- Prove2me | solution 1 for PermanentFormulaLowerBound.Formula.contractedSkeletonRootGenerators_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:13.22648+00:00
-- url     : https://prove2.me/submissions/888f8f5a-e20d-494d-a771-b6736314a4b4

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
    (w : ContractedSkeleton f) :
    IntermediateField.adjoin F (w.generators : Set _) ≤
      IntermediateField.adjoin F
        (↑(contractedSkeletonRootGenerators w) :
          Set (FractionRing (MvPolynomial Z F))) := by
  classical
  apply IntermediateField.adjoin.mono
  intro x hx
  change x ∈ w.generators at hx
  change x ∈ contractedSkeletonRootGenerators w
  unfold contractedSkeletonRootGenerators
  exact Finset.mem_union_right _ hx
end PermanentFormulaLowerBound.Formula
