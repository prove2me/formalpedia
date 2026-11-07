-- Prove2me | solution 1 for QEC.Coding.BalancedProduct.PKDistance.quotientMinimumDistance_ge_of_smallSetExpanding
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:21:46.387234+00:00
-- url     : https://prove2.me/submissions/54c83db6-5e5c-4c2c-b792-1ffea559f2b0

import Definitions.Def_QEC_Coding_BalancedProduct_HorizontalSubsystem
import Definitions.Def_QEC_Coding_BalancedProduct_LiftedProductDuality
import Definitions.Def_QEC_Coding_BalancedProduct_TannerExpansion
import Definitions.Def_QEC_Coding_CodeReduction_Classical_Distance
import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
import Definitions.Def_QEC_Coding_BalancedProduct_PKDistance
import Theorems.Thm_QEC_Coding_BalancedProduct_PKDistance_HammingWeight_constantOrbitWord
import Theorems.Thm_QEC_Coding_BalancedProduct_PKDistance_tannerAction_constantOrbitWord

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.PKDistance
open QEC.Coding
universe u v w
namespace QEC.Coding.BalancedProduct.PKDistance
theorem _root_.solution
    {G aRow aCol : Type} [Group G] [Fintype G] [DecidableEq G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    (A : Matrix aRow aCol (MonoidAlgebra (ZMod 2) G))
    {actualDistance distanceLowerBound expansionNumerator
      expansionDenominator : Nat}
    (hMinimum : MinimumDistance
      (HorizontalSubsystem.quotientTannerComplex A).middleCycleCode
        actualDistance)
    (hNumeratorPositive : 0 < expansionNumerator)
    (hExpansion : (tannerAction A).SmallSetExpanding
      (Fintype.card G * distanceLowerBound)
      expansionNumerator expansionDenominator) :
    distanceLowerBound ≤ actualDistance := by
  by_contra hLower
  have hDistanceLt : actualDistance < distanceLowerBound := Nat.lt_of_not_ge hLower
  rcases hMinimum with ⟨z, hz, hzNe, hzWeight, _hLeast⟩
  let lifted := constantOrbitWord (G := G) z
  have hLiftedWeight : HammingWeight lifted =
      Fintype.card G * actualDistance := by
    rw [HammingWeight_constantOrbitWord, hzWeight]
  have hRadius : HammingWeight lifted ≤
      Fintype.card G * distanceLowerBound := by
    rw [hLiftedWeight]
    exact Nat.mul_le_mul_left _ (Nat.le_of_lt hDistanceLt)
  have hzBoundary : HorizontalSubsystem.quotientBoundary A z = 0 :=
    ((HorizontalSubsystem.quotientTannerComplex A).mem_middleCycleCode_iff z).1 hz
  have hLiftedBoundary : tannerAction A lifted = 0 := by
    rw [tannerAction_constantOrbitWord, hzBoundary]
    rfl
  have hExpanded := hExpansion.2 lifted hRadius
  rw [hLiftedBoundary, HammingWeight_zero, Nat.mul_zero] at hExpanded
  have hzWeightPositive : 0 < HammingWeight z := by
    exact Nat.pos_of_ne_zero ((HammingWeight_eq_zero_iff z).not.mpr hzNe)
  have hGroupPositive : 0 < Fintype.card G := Fintype.card_pos
  have hLiftedWeightPositive : 0 < HammingWeight lifted := by
    rw [HammingWeight_constantOrbitWord]
    exact Nat.mul_pos hGroupPositive hzWeightPositive
  have hExpandedPositive :
      0 < expansionNumerator * HammingWeight lifted :=
    Nat.mul_pos hNumeratorPositive hLiftedWeightPositive
  omega
end QEC.Coding.BalancedProduct.PKDistance
