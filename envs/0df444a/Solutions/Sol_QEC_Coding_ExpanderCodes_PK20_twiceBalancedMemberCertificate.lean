-- Prove2me | solution 1 for QEC.Coding.ExpanderCodes.PK20.twiceBalancedMemberCertificate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T11:31:38.151976+00:00
-- url     : https://prove2.me/submissions/4baaf5d2-1ee9-4052-a8e6-643d6fa07329

import Definitions.Def_QEC_Coding_BalancedProduct_HorizontalSubsystem
import Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_Dimension
import Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_Locality
import Definitions.Def_QEC_Coding_ExpanderCodes_TwoStepBalancing
import Theorems.Thm_QEC_Coding_ExpanderCodes_PK20_card_twiceBalanced_qubits
import Theorems.Thm_QEC_Coding_ExpanderCodes_PK20_twiceBalanced_distanceBounds
import Theorems.Thm_QEC_Coding_ExpanderCodes_PK20_twiceBalanced_dimensionLowerBound
import Theorems.Thm_QEC_Coding_ExpanderCodes_PK20_twiceBalanced_boundedLocality
import Theorems.Thm_QEC_Coding_ExpanderCodes_PK20_twiceBalanced_sourceValid

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ExpanderCodes QEC.Coding.ExpanderCodes.PK20
open QEC.Coding
open QEC.Coding.DistanceBalancing
universe u
variable {xZero xOne xTwo bitOne checkOne bitTwo checkTwo : Type u}
variable [Fintype xZero] [DecidableEq xZero]
variable [Fintype xOne] [DecidableEq xOne]
variable [Fintype xTwo] [DecidableEq xTwo]
variable [Fintype bitOne] [DecidableEq bitOne]
variable [Fintype checkOne] [DecidableEq checkOne]
variable [Fintype bitTwo] [DecidableEq bitTwo]
variable [Fintype checkTwo] [DecidableEq checkTwo]
namespace QEC.Coding.ExpanderCodes.PK20
theorem _root_.solution
    (X : ChainComplexData (ZMod 2)
      (Word (ZMod 2) xZero) (Word (ZMod 2) xOne) (Word (ZMod 2) xTwo))
    (Y₁ : Word (ZMod 2) bitOne →ₗ[ZMod 2] Word (ZMod 2) checkOne)
    (Y₂ : Word (ZMod 2) bitTwo →ₗ[ZMod 2] Word (ZMod 2) checkTwo)
    {sourceDimension classicalDimensionOne classicalDimensionTwo
      sourceDistance classicalDistanceOne classicalDistanceTwo
      sourceLocality classicalLocalityOne classicalLocalityTwo : Nat}
    (hSourceDimension : sourceDimension ≤
      Module.finrank (ZMod 2) X.middleHomology)
    (hClassicalDimensionOne : classicalDimensionOne ≤
      Module.finrank (ZMod 2) (LinearMap.ker Y₁))
    (hClassicalDimensionTwo : classicalDimensionTwo ≤
      Module.finrank (ZMod 2) (LinearMap.ker Y₂))
    (hSurjectiveOne : Function.Surjective Y₁)
    (hSurjectiveTwo : Function.Surjective Y₂)
    (hHomology : MiddleHomologyDistanceAtLeast X sourceDistance)
    (hCohomology : MiddleCohomologyDistanceAtLeast X sourceDistance)
    (hClassicalOne : ClassicalDistanceAtLeast
      (LinearMap.toMatrix' Y₁) classicalDistanceOne)
    (hClassicalTwo : ClassicalDistanceAtLeast
      (LinearMap.toMatrix' Y₂) classicalDistanceTwo)
    (hSourceLocality : BoundedLocality
      (QEC.QLDPC.chainComplexBoundaryIncidence X).localityProfile sourceLocality)
    (hRowOne : ∀ b, HammingWeight
      (wordLinearMapTranspose Y₁ (Pi.single b 1)) ≤ classicalLocalityOne)
    (hColumnOne : ∀ a, HammingWeight
      (Y₁ (Pi.single a 1)) ≤ classicalLocalityOne)
    (hRowTwo : ∀ b, HammingWeight
      (wordLinearMapTranspose Y₂ (Pi.single b 1)) ≤ classicalLocalityTwo)
    (hColumnTwo : ∀ a, HammingWeight
      (Y₂ (Pi.single a 1)) ≤ classicalLocalityTwo) :
    TwiceBalancedMemberCertificate X Y₁ Y₂
      sourceDimension classicalDimensionOne classicalDimensionTwo
      sourceDistance classicalDistanceOne classicalDistanceTwo
      (sourceLocality + classicalLocalityOne + classicalLocalityTwo) := by
  have hDistances := twiceBalanced_distanceBounds X Y₁ Y₂
    hSurjectiveOne hSurjectiveTwo hHomology hCohomology
    hClassicalOne hClassicalTwo
  have hDimensionRaw := twiceBalanced_dimensionLowerBound X Y₁ Y₂
  have hDimension :
      sourceDimension * classicalDimensionOne * classicalDimensionTwo ≤
        Module.finrank (ZMod 2) (twiceBalancedComplex X Y₁ Y₂).middleHomology := by
    exact (Nat.mul_le_mul
      (Nat.mul_le_mul hSourceDimension hClassicalDimensionOne)
      hClassicalDimensionTwo).trans hDimensionRaw
  exact ⟨twiceBalanced_sourceValid X Y₁ Y₂,
    card_twiceBalanced_qubits X Y₁ Y₂,
    hDimension, hDistances.1, hDistances.2,
    twiceBalanced_boundedLocality X Y₁ Y₂ hSourceLocality
      hRowOne hColumnOne hRowTwo hColumnTwo⟩
end QEC.Coding.ExpanderCodes.PK20
