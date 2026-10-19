-- Prove2me | solution 1 for PermanentFormulaLowerBound.Formula.contractedSkeletonRootGenerators_parameter_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:13.22648+00:00
-- url     : https://prove2.me/submissions/cecb3bff-d122-44d7-9fb2-579a73ce60c5

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
    (w : ContractedSkeleton f)
    {a : FractionRing (MvPolynomial Z F)}
    (ha : a ∈ contractedSkeletonRootExtras w) :
    a ∈ IntermediateField.adjoin F
      (↑(contractedSkeletonRootGenerators w) :
        Set (FractionRing (MvPolynomial Z F))) := by
  classical
  apply IntermediateField.subset_adjoin F
    (↑(contractedSkeletonRootGenerators w) :
      Set (FractionRing (MvPolynomial Z F)))
  change a ∈ contractedSkeletonRootGenerators w
  unfold contractedSkeletonRootGenerators
  exact Finset.mem_union_left _ ha
end PermanentFormulaLowerBound.Formula
