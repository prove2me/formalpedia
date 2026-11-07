-- Prove2me | solution 1 for QEC.Coding.BalancedProduct.PKDistance.nonzero_horizontalClass_caseOne_invGenerator_weight_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:36:44.96545+00:00
-- url     : https://prove2.me/submissions/4aba56a0-e954-47bc-9088-a15afa6e7e30

import Definitions.Def_QEC_Coding_BalancedProduct_HorizontalSubsystem
import Definitions.Def_QEC_Coding_BalancedProduct_LiftedProductDuality
import Definitions.Def_QEC_Coding_BalancedProduct_TannerExpansion
import Definitions.Def_QEC_Coding_CodeReduction_Classical_Distance
import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
import Definitions.Def_QEC_Coding_BalancedProduct_PKDistance
import Theorems.Thm_QEC_Coding_BalancedProduct_PKDistance_HammingWeight_eq_horizontalPart_add_verticalPart
import Theorems.Thm_QEC_Coding_BalancedProduct_PKDistance_verticalPart_lowerBound_of_nonzero_horizontalClass_invGenerator

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.PKDistance
open QEC.Coding
universe u v w
namespace QEC.Coding.BalancedProduct.PKDistance
theorem _root_.solution
    {aRow aCol : Type}
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    (q : Nat) [NeZero q]
    (A : Matrix aRow aCol
      (MonoidAlgebra (ZMod 2) (Cyclic.CyclicGroup q)))
    (z : Word (ZMod 2)
      (LiftedProduct.QubitIndex aRow aCol Unit Unit (Cyclic.CyclicGroup q)))
    (hz : z ∈ (LiftedProduct.chainComplex
      (Cyclic.liftedProductData A
        (Cyclic.cyclicGenerator q)⁻¹)).middleCycleCode.carrier)
    {d : Nat}
    (hMinimum : MinimumDistance
      (HorizontalSubsystem.quotientTannerComplex A).middleCycleCode d)
    (hProjected : HorizontalSubsystem.horizontalHomologyProjection A
      (Cyclic.cyclicGenerator q)⁻¹
      ((LiftedProduct.chainComplex
        (Cyclic.liftedProductData A
          (Cyclic.cyclicGenerator q)⁻¹)).middleBoundaryInCycles.mkQ
            ⟨z, hz⟩) ≠ 0)
    (expansionNumerator expansionDenominator : Nat)
    (hd : 0 < d)
    (hExpansion : (tannerAction A).SmallSetExpanding
      (q * d) expansionNumerator expansionDenominator) :
    expansionNumerator * (q * d) ≤
      max (2 * expansionNumerator) (4 * expansionDenominator) *
        HammingWeight z := by
  let horizontalWeight := HammingWeight (horizontalPart z)
  let verticalWeight := HammingWeight (verticalPart z)
  have hsplit : HammingWeight z = horizontalWeight + verticalWeight :=
    HammingWeight_eq_horizontalPart_add_verticalPart z
  have hhorizontal : horizontalWeight ≤ HammingWeight z := by omega
  have hvertical : verticalWeight ≤ HammingWeight z := by omega
  by_cases hlarge : q * d ≤ 2 * horizontalWeight
  · calc
      expansionNumerator * (q * d) ≤
          expansionNumerator * (2 * horizontalWeight) :=
        Nat.mul_le_mul_left expansionNumerator hlarge
      _ = (2 * expansionNumerator) * horizontalWeight := by ac_rfl
      _ ≤ max (2 * expansionNumerator) (4 * expansionDenominator) *
          horizontalWeight :=
        Nat.mul_le_mul_right horizontalWeight (Nat.le_max_left _ _)
      _ ≤ max (2 * expansionNumerator) (4 * expansionDenominator) *
          HammingWeight z := Nat.mul_le_mul_left _ hhorizontal
  · have htwice : q * d ≤ 2 * (q * d - horizontalWeight) := by omega
    have hforced : expansionNumerator * (q * d - horizontalWeight) ≤
        2 * expansionDenominator * verticalWeight := by
      exact verticalPart_lowerBound_of_nonzero_horizontalClass_invGenerator
        q A z hz hMinimum hProjected horizontalWeight expansionNumerator
          expansionDenominator hd (by rfl) hExpansion
    calc
      expansionNumerator * (q * d) ≤
          expansionNumerator * (2 * (q * d - horizontalWeight)) :=
        Nat.mul_le_mul_left expansionNumerator htwice
      _ = 2 * (expansionNumerator * (q * d - horizontalWeight)) := by ac_rfl
      _ ≤ 2 * (2 * expansionDenominator * verticalWeight) :=
        Nat.mul_le_mul_left 2 hforced
      _ = (4 * expansionDenominator) * verticalWeight := by ring
      _ ≤ max (2 * expansionNumerator) (4 * expansionDenominator) *
          verticalWeight :=
        Nat.mul_le_mul_right verticalWeight (Nat.le_max_right _ _)
      _ ≤ max (2 * expansionNumerator) (4 * expansionDenominator) *
          HammingWeight z := Nat.mul_le_mul_left _ hvertical
end QEC.Coding.BalancedProduct.PKDistance
