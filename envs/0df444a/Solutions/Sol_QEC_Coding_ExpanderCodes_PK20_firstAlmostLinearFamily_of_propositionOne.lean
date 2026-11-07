-- Prove2me | solution 1 for QEC.Coding.ExpanderCodes.PK20.firstAlmostLinearFamily_of_propositionOne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:46:28.825029+00:00
-- url     : https://prove2.me/submissions/879edca9-764b-48ad-9c40-90ab7693dcbe

import Definitions.Def_QEC_Coding_BalancedProduct_PKDistance
import Definitions.Def_QEC_Coding_BalancedProduct_CyclicLocality
import Definitions.Def_QEC_Coding_BalancedProduct_CyclicDimension
import Definitions.Def_QEC_Coding_ExpanderCodes_AlmostLinear
import Theorems.Thm_QEC_Coding_ExpanderCodes_PK20_firstFamilyMember_of_propositionOne_output
import Theorems.Thm_QEC_Coding_ExpanderCodes_PK20_familyLift_odd
import Theorems.Thm_QEC_Coding_ExpanderCodes_PK20_familyLift_gt
import Theorems.Thm_QEC_Coding_ExpanderCodes_PK20_two_pow_radiusDenominator_le_familyLift
import Theorems.Thm_QEC_Coding_ExpanderCodes_PK20_liftScale_le_familyLift

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ExpanderCodes QEC.Coding.ExpanderCodes.PK20
open QEC.Coding
open QEC.Coding.BalancedProduct
namespace QEC.Coding.ExpanderCodes.PK20
theorem _root_.solution
    (hPropositionOne : PropositionOneExpandingMatrixFamily) :
    FirstAlmostLinearFamily := by
  rcases hPropositionOne with
    ⟨w, gamma, radiusNumerator, radiusDenominator,
      expansionNumerator, expansionDenominator,
      hw4, hgamma, hRadiusNumerator, hRadiusDenominator,
      hExpansionNumerator, hExpansionDenominator, hMatrices⟩
  refine ⟨w, gamma, radiusNumerator, radiusDenominator,
    expansionNumerator, expansionDenominator,
    hw4, hgamma, hRadiusNumerator, hRadiusDenominator,
    hExpansionNumerator, hExpansionDenominator, ?_⟩
  intro B
  let q := familyLift w radiusDenominator B
  have hqOdd : Odd q := familyLift_odd w radiusDenominator B
  have hqTwo : 1 < q := by
    unfold q familyLift
    have hPowPositive : 0 < 2 ^ radiusDenominator := pow_pos (by norm_num) _
    omega
  letI : NeZero q := ⟨by omega⟩
  obtain ⟨n, m, A, hm, hnLower, hnUpper,
      hForwardWeight, hTransposeWeight,
      hForwardRelative, hTransposeRelative⟩ := hMatrices q hqTwo
  have hDenominatorLog : radiusDenominator ≤ Nat.log 2 q := by
    apply Nat.le_log_of_pow_le (by norm_num)
    exact two_pow_radiusDenominator_le_familyLift w radiusDenominator B
  have hDenominatorLeN : radiusDenominator ≤ n := by
    have hGammaOne : 1 ≤ gamma := hgamma
    calc
      radiusDenominator ≤ Nat.log 2 q := hDenominatorLog
      _ ≤ gamma * Nat.log 2 q := Nat.le_mul_of_pos_left _ hgamma
      _ ≤ n := hnLower
  have hLiftLarge : 2 * w * radiusDenominator ≤ q :=
    liftScale_le_familyLift w radiusDenominator B
  refine ⟨q, n, m, inferInstance, A, familyLift_gt w radiusDenominator B, ?_⟩
  exact firstFamilyMember_of_propositionOne_output
    w gamma radiusNumerator radiusDenominator
      expansionNumerator expansionDenominator q n m A
    hw4 hgamma hRadiusNumerator hRadiusDenominator
      hExpansionNumerator hExpansionDenominator hqOdd hm hnLower hnUpper
      hDenominatorLeN hLiftLarge hForwardWeight hTransposeWeight
      hForwardRelative hTransposeRelative
end QEC.Coding.ExpanderCodes.PK20
