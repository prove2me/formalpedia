-- Prove2me | solution 1 for PermanentRollout.sourceBlockMatchingOf_sum_weight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:06.641753+00:00
-- url     : https://prove2.me/submissions/8b12c8cb-3303-4ddf-9cc3-f89e87fe9a23

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_sourceBlockMatchingOf_weight
import Theorems.Thm_PermanentRollout_sourceBlock_ones_matching_card
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
namespace MvPolynomial.IsWeightedHomogeneous
end MvPolynomial.IsWeightedHomogeneous
namespace Finset
end Finset
namespace PermanentCircuitCompatibility
end PermanentCircuitCompatibility
namespace PermanentRollout
section Standalone_PermanentRolloutRoot
open scoped BigOperators
end Standalone_PermanentRolloutRoot
section Standalone_Geometry
open scoped BigOperators
end Standalone_Geometry
section Standalone_Bezout
end Standalone_Bezout
section Standalone_FiberDimension
open Ideal
variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
end Standalone_FiberDimension
section Standalone_GenericAvoidance
open Set Filter Module
open scoped BigOperators ENNReal
noncomputable section
section HomogeneousPrimeInputAvoidance
attribute [local instance] MvPolynomial.gradedAlgebra
end HomogeneousPrimeInputAvoidance
end
end Standalone_GenericAvoidance
section Standalone_FiniteMaps
end Standalone_FiniteMaps
section Standalone_HomogeneousFiniteness
open scoped BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra
section FractionField
end FractionField
end Standalone_HomogeneousFiniteness
section Standalone_LeadingForms
open scoped BigOperators
end Standalone_LeadingForms
section Standalone_ProjectiveDimension
open scoped LinearAlgebra.Projectivization
section AlgebraicProjectiveLeadingForms
attribute [local instance] MvPolynomial.gradedAlgebra
end AlgebraicProjectiveLeadingForms
end Standalone_ProjectiveDimension
noncomputable section Standalone_ProjectiveSlicing
open scoped BigOperators LinearAlgebra.Projectivization
attribute [local instance] MvPolynomial.gradedAlgebra
end Standalone_ProjectiveSlicing
section Standalone_MultivariateBezout
open scoped nonZeroDivisors Pointwise
attribute [local instance] MvPolynomial.gradedAlgebra
open scoped BigOperators
open scoped BigOperators
open scoped Pointwise
attribute [local instance] MvPolynomial.gradedAlgebra
open scoped BigOperators
open scoped BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra
open scoped BigOperators
open scoped BigOperators
open scoped Pointwise BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra
open scoped Pointwise BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra
open scoped Pointwise BigOperators
open scoped BigOperators
open scoped Pointwise
open scoped BigOperators
open scoped Pointwise
attribute [local instance] MvPolynomial.gradedAlgebra
open scoped BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra
open scoped Pointwise BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra
open scoped Pointwise BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra
open scoped TensorProduct
end Standalone_MultivariateBezout
noncomputable section Standalone_FreeAffine
open scoped BigOperators
namespace FreeAffineForm
end FreeAffineForm
namespace FreeAffineInput
end FreeAffineInput
namespace FreeAffineForm
end FreeAffineForm
namespace FreeAffineInstruction
end FreeAffineInstruction
namespace FreeAffineCircuit
end FreeAffineCircuit
end Standalone_FreeAffine
noncomputable section Standalone_ReverseMode
open scoped BigOperators
namespace ReverseAdjoint
namespace CircuitAdjoint
end CircuitAdjoint
namespace CircuitAdjoint
end CircuitAdjoint
end ReverseAdjoint
end Standalone_ReverseMode
section Standalone_AffineBezout
open scoped BigOperators Topology Pointwise
open Filter Asymptotics
attribute [local instance] MvPolynomial.gradedAlgebra
end Standalone_AffineBezout
section Standalone_ParameterBounds
end Standalone_ParameterBounds
section Standalone_Asymptotics
end Standalone_Asymptotics
section Standalone_BlockPermanent
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq
private theorem sourceBlock_weighted_double_sum
    {α β R : Type*} [Fintype α] [Fintype β] [CommSemiring R]
    (c : R) (f : α → R) (g : β → R) :
    (∑ a : α, ∑ b : β, c * (f a * g b)) =
      c * ((∑ a : α, f a) * (∑ b : β, g b)) := by
  rw [Fintype.sum_mul_sum]
  simp_rw [Finset.mul_sum]
end Standalone_BlockPermanent
section Standalone_CircuitDAG
end Standalone_CircuitDAG
section Standalone_Combinatorics
open scoped BigOperators
end Standalone_Combinatorics
section Standalone_SquareZero
open scoped BigOperators
end Standalone_SquareZero
section Standalone_Subtree
open scoped BigOperators
namespace BlockTree
end BlockTree
end Standalone_Subtree
section Standalone_Coefficients
open scoped BigOperators
end Standalone_Coefficients
section Standalone_Partition
open scoped BigOperators
end Standalone_Partition
section Standalone_PartitionMatching
open scoped BigOperators
end Standalone_PartitionMatching
section Standalone_PartitionInversion
open scoped BigOperators
end Standalone_PartitionInversion
section Standalone_Incidence
open scoped BigOperators
end Standalone_Incidence
section Standalone_SourceCircuitBridge
open scoped BigOperators
noncomputable section
end
end Standalone_SourceCircuitBridge
section Standalone_TreeCoefficients
open scoped BigOperators
end Standalone_TreeCoefficients
section Standalone_SourcePermanentSpecialization
open scoped BigOperators
noncomputable section
end
end Standalone_SourcePermanentSpecialization
section Standalone_MainReduction
open scoped BigOperators
noncomputable section
namespace CircuitPrefix
end CircuitPrefix
namespace ArithmeticCircuit
end ArithmeticCircuit
open scoped LinearAlgebra.Projectivization
end
end Standalone_MainReduction
end PermanentRollout
namespace PermanentFormulaLowerBound
universe u v w
open scoped BigOperators Kronecker Matrix IntermediateField.algebraAdjoinAdjoin
namespace TranscendenceBounds
end TranscendenceBounds
namespace Formula
variable {ι : Type u} {R : Type v}
end Formula
namespace RationalFormula
variable {ι : Type u} {R : Type v}
end RationalFormula
namespace RationalFormula
noncomputable section RationalSkeletonInduction
variable {Y Z F : Type*}
end RationalSkeletonInduction
end RationalFormula
namespace Formula
end Formula
namespace Formula
end Formula
namespace RationalFormula
end RationalFormula
namespace Formula
end Formula
namespace RationalFormula
end RationalFormula
section Coefficients
variable {Y : Type u} {Z : Type v} {F : Type w} [Field F]
end Coefficients
section Jacobian
variable {ι : Type u} {κ : Type v} {F : Type w}
end Jacobian
noncomputable section PolynomialIntersection
variable {K E ι : Type*} [Field K] [Field E] [Algebra K E]
end PolynomialIntersection
noncomputable section RationalCoefficientExtraction
variable {F E Y : Type*} [Field F] [Field E] [Algebra F E]
end RationalCoefficientExtraction
noncomputable section RationalSkeleton
variable {E L : Type*} [Field E] [Field L] [Algebra E L]
end RationalSkeleton
namespace RationalFormula
noncomputable section RationalSkeletonContraction
variable {Y Z F : Type*}
section MarkedPathGates
variable {E L : Type*} [Field E] [Field L] [Algebra E L]
end MarkedPathGates
namespace ContractedRationalSkeleton
end ContractedRationalSkeleton
end RationalSkeletonContraction
end RationalFormula
namespace Formula
variable {Y : Type u} {Z : Type v} {F : Type w}
section CoefficientFields
variable [Field F]
end CoefficientFields
end Formula
namespace Formula
variable {ι : Type u} {κ : Type v} {R : Type w}
end Formula
namespace RationalFormula
variable {ι : Type u} {κ : Type v} {R : Type w}
end RationalFormula
namespace Formula
end Formula
namespace RationalFormula
end RationalFormula
end PermanentFormulaLowerBound
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq
namespace PermanentRollout
theorem _root_.solution
    {R : Type*} [CommSemiring R] (r s d : ℕ)
    (X : Matrix (Fin r) (Fin s) R)
    (U : Matrix (Fin r) (Fin (r - d)) R)
    (I : Finset (Fin r)) (J : Finset (Fin s))
    (hJ : J.card = d) :
    (∑ variableMatching : I ≃ J,
      ∑ constantMatching :
        {row : Fin r // row ∉ I} ≃ Fin (r - d),
      ∑ onesMatching :
        Fin (s - d) ≃ {column : Fin s // column ∉ J},
        ∏ row, sourceBlockMatrix r s d X U row
          (sourceBlockMatchingOf r s d I J
            variableMatching constantMatching onesMatching row)) =
      ((s - d).factorial : R) *
        (sourceBlockAlpha r d U I * sourceBlockMinor r s X I J) := by
  simp_rw [sourceBlockMatchingOf_weight]
  simp_rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
  rw [sourceBlock_ones_matching_card s d J hJ]
  rw [sourceBlock_weighted_double_sum]
  unfold sourceBlockAlpha sourceBlockMinor
  congr 1
  apply mul_comm
end PermanentRollout
