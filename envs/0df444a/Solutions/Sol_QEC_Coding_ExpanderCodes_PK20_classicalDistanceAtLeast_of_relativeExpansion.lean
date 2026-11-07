-- Prove2me | solution 1 for QEC.Coding.ExpanderCodes.PK20.classicalDistanceAtLeast_of_relativeExpansion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:23:47.134482+00:00
-- url     : https://prove2.me/submissions/7bc57a84-30e5-4652-8e75-4496d13875b4

import Definitions.Def_QEC_Coding_ExpanderCodes_AlmostLinear
import Definitions.Def_QEC_Coding_ExpanderCodes_ClassicalRowReduction
import Definitions.Def_QEC_Coding_ExpanderCodes_ClassicalFactor

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ExpanderCodes QEC.Coding.ExpanderCodes.PK20
open QEC.Coding
open QEC.Coding.BalancedProduct
open QEC.Coding.DistanceBalancing
namespace QEC.Coding.ExpanderCodes.PK20
theorem _root_.solution
    {bit check : Type}
    [Fintype bit] [DecidableEq bit]
    [Fintype check] [DecidableEq check]
    (Y : Word (ZMod 2) bit →ₗ[ZMod 2] Word (ZMod 2) check)
    {radiusNumerator radiusDenominator
      expansionNumerator expansionDenominator : Nat}
    (hExpansionNumerator : 0 < expansionNumerator)
    (hExpansion : Y.SmallSetExpandingAtRelativeRadius
      radiusNumerator radiusDenominator
      expansionNumerator expansionDenominator) :
    ClassicalDistanceAtLeast (LinearMap.toMatrix' Y)
      (classicalDistanceLowerBound (Fintype.card bit)
        radiusNumerator radiusDenominator) := by
  intro x hx hne
  rw [Matrix.toLin'_toMatrix'] at hx
  by_contra hSmall
  have hWeightLe : HammingWeight x ≤
      classicalDistanceLowerBound (Fintype.card bit)
        radiusNumerator radiusDenominator := by omega
  have hRadius : radiusDenominator * HammingWeight x ≤
      radiusNumerator * Fintype.card bit := by
    exact (Nat.mul_le_mul_left radiusDenominator hWeightLe).trans
      (Nat.mul_div_le _ _)
  have hExpanded := hExpansion.2.2 x hRadius
  rw [hx, HammingWeight_zero, Nat.mul_zero] at hExpanded
  have hWeightZero : HammingWeight x = 0 := by
    rcases Nat.mul_eq_zero.mp (Nat.eq_zero_of_le_zero hExpanded) with
      hNumeratorZero | hWeightZero
    · exact (Nat.ne_of_gt hExpansionNumerator hNumeratorZero).elim
    · exact hWeightZero
  exact hne ((HammingWeight_eq_zero_iff x).mp hWeightZero)
end QEC.Coding.ExpanderCodes.PK20
