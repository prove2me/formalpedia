-- Prove2me | solution 1 for PermanentRollout.permanent_circuit_loglog_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:11.481307+00:00
-- url     : https://prove2.me/submissions/0e16082f-55da-481a-a662-75f721a448d0

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_le_two_mul_blockColumns
import Theorems.Thm_PermanentRollout_real_le_circuitComplexity_iff
import Theorems.Thm_PermanentRollout_source_fixedDegree_permanent_circuit_logarithmic_bound
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
private theorem six_mul_le_two_pow_of_sixteen_le {k : ℕ} (hk : 16 ≤ k) :
    6 * k ≤ 2 ^ k := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
      rw [pow_succ]
      omega
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
noncomputable section
open scoped LinearAlgebra.Projectivization
namespace PermanentRollout
theorem _root_.solution {n : ℕ} (hn : 2 ^ 16 ≤ n) :
    (n : ℝ) ^ 2 * (Real.logb 2 (Real.logb 2 (n : ℝ)) - 3) / 144 ≤
      (circuitComplexity (permanent n) : ℝ) := by
  let L : ℕ := Nat.log 2 n
  let d : ℕ := L / 4
  have hnzero : n ≠ 0 := by omega
  have hL : 16 ≤ L := by
    exact (Nat.le_log_iff_pow_le (by norm_num) hnzero).2 hn
  have hd : 4 ≤ d := by
    dsimp [d]
    omega
  have hwidth : 4 * d ≤ L := by
    dsimp [d]
    omega
  have hpower : 2 ^ (4 * d) ≤ n := by
    exact Nat.pow_le_of_le_log hnzero hwidth
  have hlarge : 6 * blockWidth d ≤ n := by
    have hlinear : 6 * L ≤ 2 ^ L := six_mul_le_two_pow_of_sixteen_le hL
    have hlogpower : 2 ^ L ≤ n := Nat.pow_log_le_self 2 hnzero
    dsimp [blockWidth]
    omega
  have hrho : powerSumParameter d ≤ n := by
    dsimp [powerSumParameter, blockWidth]
    omega
  have hscale : 4 * powerSumParameter d ≤ blockWidth d * blockColumns n d := by
    have hcolumns := le_two_mul_blockColumns n d
    have hwidth' : 8 ≤ blockWidth d := by
      dsimp [blockWidth]
      omega
    nlinarith [Nat.mul_le_mul_left 4 hrho,
      Nat.mul_le_mul_right (blockColumns n d) hwidth']
  have hcomplexity :
      (n : ℝ) ^ 2 * Real.logb 2 ((d : ℝ) - 1) / 144 ≤
        (circuitComplexity (permanent n) : ℝ) := by
    apply (real_le_circuitComplexity_iff (permanent n) _).2
    intro circuit hcircuit
    exact source_fixedDegree_permanent_circuit_logarithmic_bound circuit
      (by omega) hlarge hscale hcircuit
  have hlogpos : 0 < Real.logb 2 (n : ℝ) := by
    apply Real.logb_pos (by norm_num)
    exact_mod_cast (show 1 < n by omega)
  have hloglt : Real.logb 2 (n : ℝ) < (L + 1 : ℕ) := by
    have hpowlt : n < 2 ^ (L + 1) := by
      simpa [L] using Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) n
    have hcast : (n : ℝ) < (2 : ℝ) ^ (L + 1) := by
      exact_mod_cast hpowlt
    calc
      Real.logb 2 (n : ℝ) < Real.logb 2 ((2 : ℝ) ^ (L + 1)) :=
        Real.logb_lt_logb (by norm_num) (by exact_mod_cast (show 0 < n by omega)) hcast
      _ = (L + 1 : ℕ) := by norm_num [Real.logb_pow]
  have hLd : L + 1 ≤ 8 * (d - 1) := by
    have hrem := Nat.mod_lt L (by omega : 0 < (4 : ℕ))
    have hdecomp := Nat.mod_add_div L 4
    dsimp [d]
    omega
  have hinner : Real.logb 2 (n : ℝ) / 8 ≤ (d : ℝ) - 1 := by
    have hcast : ((L + 1 : ℕ) : ℝ) ≤ (8 * (d - 1) : ℕ) := by
      exact_mod_cast hLd
    have hcastsub : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ d)]
      norm_num
    push_cast at hcast
    push_cast at hloglt
    rw [hcastsub] at hcast
    linarith
  have hlog8 : Real.logb 2 (8 : ℝ) = 3 := by
    calc
      Real.logb 2 (8 : ℝ) = Real.logb 2 ((2 : ℝ) ^ (3 : ℕ)) := by norm_num
      _ = 3 := by rw [Real.logb_pow]; norm_num
  have hlogcompare :
      Real.logb 2 (Real.logb 2 (n : ℝ)) - 3 ≤
        Real.logb 2 ((d : ℝ) - 1) := by
    calc
      Real.logb 2 (Real.logb 2 (n : ℝ)) - 3 =
          Real.logb 2 (Real.logb 2 (n : ℝ) / 8) := by
            rw [Real.logb_div (ne_of_gt hlogpos) (by norm_num), hlog8]
      _ ≤ Real.logb 2 ((d : ℝ) - 1) :=
        Real.logb_le_logb_of_le (by norm_num)
          (div_pos hlogpos (by norm_num)) hinner
  calc
    (n : ℝ) ^ 2 * (Real.logb 2 (Real.logb 2 (n : ℝ)) - 3) / 144 ≤
        (n : ℝ) ^ 2 * Real.logb 2 ((d : ℝ) - 1) / 144 := by
          gcongr
    _ ≤ (circuitComplexity (permanent n) : ℝ) := hcomplexity
end PermanentRollout
