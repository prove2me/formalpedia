-- Prove2me | solution 1 for PermanentFormulaLowerBound.Formula.contractedSkeletonRootGenerators_coeff_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:13.22648+00:00
-- url     : https://prove2.me/submissions/36fd4037-1551-4f4c-aaeb-94c4832cee6f

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentFormulaLowerBound_Formula_contractedSkeletonRootGenerators_le
import Theorems.Thm_PermanentFormulaLowerBound_Formula_contractedSkeletonRootGenerators_parameter_mem

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
    (w : ContractedSkeleton f) (α : Y →₀ ℕ) :
    algebraMap (MvPolynomial Z F) (FractionRing (MvPolynomial Z F))
        (MvPolynomial.coeff α (splitEval f)) ∈
      IntermediateField.adjoin F
        (↑(contractedSkeletonRootGenerators w) :
          Set (FractionRing (MvPolynomial Z F))) := by
  classical
  let S : IntermediateField F (FractionRing (MvPolynomial Z F)) :=
    IntermediateField.adjoin F
      (↑(contractedSkeletonRootGenerators w) :
        Set (FractionRing (MvPolynomial Z F)))
  change algebraMap (MvPolynomial Z F) (FractionRing (MvPolynomial Z F))
    (MvPolynomial.coeff α (splitEval f)) ∈ S
  rw [w.split_eq]
  apply coeff_mem_intermediateField_add S
  · intro β
    apply coeff_mem_intermediateField_mul S
    · apply coeff_mem_intermediateField_C S
      apply contractedSkeletonRootGenerators_parameter_mem w
      unfold contractedSkeletonRootExtras
      exact Finset.mem_insert_self _ _
    · intro γ
      exact contractedSkeletonRootGenerators_le w (w.core_coeff_mem γ)
  · apply coeff_mem_intermediateField_C S
    apply contractedSkeletonRootGenerators_parameter_mem w
    unfold contractedSkeletonRootExtras
    exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
end PermanentFormulaLowerBound.Formula
