-- Prove2me | solution 1 for QEC.Coding.ExpanderCodes.PK20.twoProductConstructionFamily_of_propositionOne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T12:06:05.213562+00:00
-- url     : https://prove2.me/submissions/c7a3c8be-1a66-4c90-82f5-1b6f17132c09

import Definitions.Def_QEC_Coding_ExpanderCodes_ClassicalFactor
import Definitions.Def_QEC_Coding_ExpanderCodes_TwoStepBalancing
import Definitions.Def_QEC_Coding_ExpanderCodes_Tradeoff
import Theorems.Thm_QEC_Coding_ExpanderCodes_PK20_tradeoff_blockLength_le
import Theorems.Thm_QEC_Coding_ExpanderCodes_PK20_tradeoffMember_of_propositionOne_outputs
import Theorems.Thm_QEC_Coding_ExpanderCodes_PK20_balancingLift_gt_one
import Theorems.Thm_QEC_Coding_ExpanderCodes_PK20_rpow_le_balancingLift
import Theorems.Thm_QEC_Coding_ExpanderCodes_PK20_familyLift_gt
import Theorems.Thm_QEC_Coding_ExpanderCodes_PK20_familyLift_odd
import Theorems.Thm_QEC_Coding_ExpanderCodes_PK20_firstFamilyMember_of_propositionOne_output
import Theorems.Thm_QEC_Coding_ExpanderCodes_PK20_liftScale_le_familyLift
import Theorems.Thm_QEC_Coding_ExpanderCodes_PK20_two_pow_radiusDenominator_le_familyLift


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ExpanderCodes QEC.Coding.ExpanderCodes.PK20
open QEC.Coding
open QEC.Coding.BalancedProduct
namespace QEC.Coding.ExpanderCodes.PK20
theorem _root_.solution
    (hPropositionOne : PropositionOneExpandingMatrixFamily) :
    TwoProductConstructionFamily := by
  rcases hPropositionOne with
    ⟨w, gamma, radiusNumerator, radiusDenominator,
      expansionNumerator, expansionDenominator,
      hw4, hgamma, hRadiusNumerator, hRadiusDenominator,
      hExpansionNumerator, hExpansionDenominator, hMatrices⟩
  refine ⟨w, gamma, radiusNumerator, radiusDenominator,
    expansionNumerator, expansionDenominator,
    hw4, hgamma, hRadiusNumerator, hRadiusDenominator,
    hExpansionNumerator, hExpansionDenominator, ?_⟩
  intro alpha hAlphaNonnegative hAlphaOne B
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
    calc
      radiusDenominator ≤ Nat.log 2 q := hDenominatorLog
      _ ≤ gamma * Nat.log 2 q := Nat.le_mul_of_pos_left _ hgamma
      _ ≤ n := hnLower
  have hLiftLarge : 2 * w * radiusDenominator ≤ q :=
    liftScale_le_familyLift w radiusDenominator B
  have hInitial := firstFamilyMember_of_propositionOne_output
    w gamma radiusNumerator radiusDenominator
      expansionNumerator expansionDenominator q n m A
    hw4 hgamma hRadiusNumerator hRadiusDenominator
      hExpansionNumerator hExpansionDenominator hqOdd hm hnLower hnUpper
      hDenominatorLeN hLiftLarge hForwardWeight hTransposeWeight
      hForwardRelative hTransposeRelative
  let r := balancingLift alpha q
  have hrTwo : 1 < r := balancingLift_gt_one alpha q
  letI : NeZero r := ⟨by omega⟩
  obtain ⟨nc, mc, C, hmc, hncLower, hncUpper,
      hFactorForwardWeight, hFactorTransposeWeight,
      hFactorForwardRelative, _hFactorTransposeRelative⟩ := hMatrices r hrTwo
  have hTradeoff := tradeoffMember_of_propositionOne_outputs
    q n m r nc mc w gamma radiusNumerator radiusDenominator
      expansionNumerator expansionDenominator A C hInitial
      hExpansionNumerator hFactorForwardWeight hFactorTransposeWeight
      hFactorForwardRelative
  have hChecks : mc ≤ w * nc := by
    rw [hmc]
    have : 2 * (w / 4) ≤ w := by omega
    nlinarith
  have hBlocklength := tradeoff_blockLength_le q n m r nc mc w A C hChecks
  exact ⟨q, n, m, r, nc, mc, inferInstance, inferInstance, A, C,
    familyLift_gt w radiusDenominator B, rfl,
    rpow_le_balancingLift alpha q,
    hncLower, hncUpper, hTradeoff, hBlocklength⟩
end QEC.Coding.ExpanderCodes.PK20
