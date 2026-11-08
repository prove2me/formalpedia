-- Prove2me | solution 1 for QEC.Coding.ExpanderCodes.PK20.twiceBalanced_dimensionLowerBound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T11:25:23.450742+00:00
-- url     : https://prove2.me/submissions/5099f4db-88b1-4627-8dcf-89ebd9b51f10

import Definitions.Def_QEC_Coding_BalancedProduct_HorizontalSubsystem
import Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_Dimension
import Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_Locality
import Definitions.Def_QEC_Coding_ExpanderCodes_TwoStepBalancing
import Theorems.Thm_QEC_Coding_DistanceBalancing_finrank_middleHomology_mul_finrank_classicalKernel_le
import Theorems.Thm_QEC_Coding_finrank_middleHomology_dual_eq_middleCohomology


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
    (Y₂ : Word (ZMod 2) bitTwo →ₗ[ZMod 2] Word (ZMod 2) checkTwo) :
    Module.finrank (ZMod 2) X.middleHomology *
        Module.finrank (ZMod 2) (LinearMap.ker Y₁) *
        Module.finrank (ZMod 2) (LinearMap.ker Y₂) ≤
      Module.finrank (ZMod 2)
        (twiceBalancedComplex X Y₁ Y₂).middleHomology := by
  have hFirst := finrank_middleHomology_mul_finrank_classicalKernel_le
    (firstBalancingData X Y₁)
  have hSecond := finrank_middleHomology_mul_finrank_classicalKernel_le
    (secondBalancingData X Y₁ Y₂)
  have hFirstCohomology :
      Module.finrank (ZMod 2) (firstBalancedComplex X Y₁).middleCohomology =
        Module.finrank (ZMod 2) (firstBalancedComplex X Y₁).middleHomology :=
    BalancedProduct.HorizontalSubsystem.finrank_middleCohomology_eq_middleHomology _
  change _ ≤ Module.finrank (ZMod 2)
    (chainComplex (secondBalancingData X Y₁ Y₂)).middleCohomology
  rw [BalancedProduct.HorizontalSubsystem.finrank_middleCohomology_eq_middleHomology]
  change _ ≤ Module.finrank (ZMod 2)
    (chainComplex (secondBalancingData X Y₁ Y₂)).middleHomology
  change Module.finrank (ZMod 2) X.middleHomology *
      Module.finrank (ZMod 2) (LinearMap.ker Y₁) *
      Module.finrank (ZMod 2) (LinearMap.ker Y₂) ≤ _
  have hFirst' : Module.finrank (ZMod 2) X.middleHomology *
      Module.finrank (ZMod 2) (LinearMap.ker Y₁) ≤
        Module.finrank (ZMod 2) (firstBalancedComplex X Y₁).middleHomology := by
    unfold firstBalancingData at hFirst
    rw [sourceChainComplex_ofComplexes] at hFirst
    change Module.finrank (ZMod 2) X.middleHomology *
        Module.finrank (ZMod 2)
          (LinearMap.ker (Matrix.toLin' (LinearMap.toMatrix' Y₁))) ≤ _ at hFirst
    rw [Matrix.toLin'_toMatrix'] at hFirst
    exact hFirst
  have hSecond' : Module.finrank (ZMod 2)
      (dualChainComplex (firstBalancedComplex X Y₁)).middleHomology *
      Module.finrank (ZMod 2) (LinearMap.ker Y₂) ≤
        Module.finrank (ZMod 2)
          (chainComplex (secondBalancingData X Y₁ Y₂)).middleHomology := by
    unfold secondBalancingData at hSecond
    rw [sourceChainComplex_ofComplexes] at hSecond
    change Module.finrank (ZMod 2)
        (dualChainComplex (firstBalancedComplex X Y₁)).middleHomology *
        Module.finrank (ZMod 2)
          (LinearMap.ker (Matrix.toLin' (LinearMap.toMatrix' Y₂))) ≤ _ at hSecond
    rw [Matrix.toLin'_toMatrix'] at hSecond
    exact hSecond
  rw [finrank_middleHomology_dual_eq_middleCohomology,
    hFirstCohomology] at hSecond'
  exact (Nat.mul_le_mul_right _ hFirst').trans hSecond'
end QEC.Coding.ExpanderCodes.PK20
