-- Prove2me | solution 1 for PermanentRollout.sourceBlockMatrix_permanent_eq_valid_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:06.641753+00:00
-- url     : https://prove2.me/submissions/c22650b4-ac49-40fa-a60e-b3594837fb09

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_sourceBlockMatrix_matching_eq_zero_of_invalid
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
private theorem sourceBlock_sum_subtype_of_zero
    {α R : Type*} [Fintype α] [CommSemiring R]
    (p : α → Prop) (f : α → R)
    (hzero : ∀ a, ¬ p a → f a = 0) :
    (∑ a : α, f a) = ∑ a : {a : α // p a}, f a.val := by
  exact Finset.sum_congr_set {a | p a} f (fun a => f a.val)
    (fun _ _ => rfl) hzero
private theorem rectangularPermanent_sum_subtype_of_zero
    {α β R : Type*} [Fintype α] [Fintype β] [CommSemiring R]
    (A : Matrix α β R) (p : (α ≃ β) → Prop)
    (hzero : ∀ matching : α ≃ β,
      ¬ p matching → (∏ row, A row (matching row)) = 0) :
    rectangularPermanent A =
      ∑ matching : {matching : α ≃ β // p matching},
        ∏ row, A row (matching.val row) := by
  unfold rectangularPermanent
  exact sourceBlock_sum_subtype_of_zero p
    (fun matching : α ≃ β => ∏ row, A row (matching row)) hzero
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
    (U : Matrix (Fin r) (Fin (r - d)) R) :
    rectangularPermanent (sourceBlockMatrix r s d X U) =
      ∑ matching : SourceBlockValidMatching r s d,
        sourceBlockMatchingWeight r s d X U matching.val := by
  have hsum := rectangularPermanent_sum_subtype_of_zero
    (sourceBlockMatrix r s d X U)
    (fun matching => ∀ row : Fin (s - d),
      ∃ column : Fin s, matching (.inr row) = .inl column)
    (fun matching hinvalid =>
      sourceBlockMatrix_matching_eq_zero_of_invalid
        r s d X U matching hinvalid)
  unfold sourceBlockMatchingWeight
  convert hsum using 1
  apply Finset.sum_congr
  · ext matching
    simp
  · intro matching _
    rfl
end PermanentRollout
