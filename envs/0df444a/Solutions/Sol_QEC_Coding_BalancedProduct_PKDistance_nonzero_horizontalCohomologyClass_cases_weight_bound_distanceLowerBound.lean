-- Prove2me | solution 1 for QEC.Coding.BalancedProduct.PKDistance.nonzero_horizontalCohomologyClass_cases_weight_bound_distanceLowerBound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:47:21.587845+00:00
-- url     : https://prove2.me/submissions/e2b9ce15-24a1-4935-a7cd-6fa7cbcbcb02

import Definitions.Def_QEC_Coding_BalancedProduct_HorizontalSubsystem
import Definitions.Def_QEC_Coding_BalancedProduct_LiftedProductDuality
import Definitions.Def_QEC_Coding_BalancedProduct_TannerExpansion
import Definitions.Def_QEC_Coding_CodeReduction_Classical_Distance
import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
import Definitions.Def_QEC_Coding_BalancedProduct_PKDistance
import Theorems.Thm_QEC_Coding_BalancedProduct_PKDistance_zero_horizontalClass_caseTwo_invGenerator_weight_bound
import Theorems.Thm_QEC_Coding_BalancedProduct_PKDistance_dualCycle_mem_invGenerator_middleCycleCode
import Theorems.Thm_QEC_Coding_BalancedProduct_PKDistance_dualCycle_not_invGenerator_boundary_of_horizontalCohomologyProjection_ne_zero
import Theorems.Thm_QEC_Coding_BalancedProduct_PKDistance_nonzero_horizontalClass_caseOne_invGenerator_weight_bound_distanceLowerBound
import Theorems.Thm_QEC_Coding_BalancedProduct_LiftedProductDuality_HammingWeight_swapWord


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.PKDistance
open QEC.Coding
universe u v w
namespace QEC.Coding.BalancedProduct.PKDistance
theorem _root_.solution
    {aRow aCol : Type}
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    (q : Nat) [NeZero q] (hq : 2 ≤ q)
    (A : Matrix aRow aCol
      (MonoidAlgebra (ZMod 2) (Cyclic.CyclicGroup q)))
    (z : Word (ZMod 2)
      (LiftedProduct.QubitIndex aRow aCol Unit Unit (Cyclic.CyclicGroup q)))
    (hz : z ∈ (LiftedProduct.chainComplex
      (Cyclic.data q A)).middleCocycleCode.carrier)
    (hProjected : HorizontalSubsystem.horizontalCohomologyProjection A
      (Cyclic.cyclicGenerator q)
      ((LiftedProduct.chainComplex
        (Cyclic.data q A)).middleCoboundaryInCocycles.mkQ ⟨z, hz⟩) ≠ 0)
    {actualDualDistance dualDistanceLowerBound : Nat}
    (hDualMinimum : MinimumDistance
      (HorizontalSubsystem.quotientTannerComplex
        (LiftedProduct.starTranspose A)).middleCycleCode actualDualDistance)
    (hDualDistanceLower : dualDistanceLowerBound ≤ actualDualDistance)
    (hDualDistanceLowerPositive : 0 < dualDistanceLowerBound)
    (w threshold expansionRadius expansionNumerator expansionDenominator : Nat)
    (hw : 0 < w) (hthreshold : 0 < threshold)
    (hThresholdScale : 2 * w * threshold ≤ q)
    (hColumnWeight : ∀ i : aRow × Cyclic.CyclicGroup q,
      HammingWeight
        (tannerAction (LiftedProduct.starTranspose A) (Pi.single i 1)) ≤ w)
    (hRadius : threshold ≤ expansionRadius)
    (hCaseOneExpansion :
      (tannerAction (LiftedProduct.starTranspose A)).SmallSetExpanding
        (q * dualDistanceLowerBound) expansionNumerator expansionDenominator)
    (hCaseTwoExpansion :
      (tannerAction (LiftedProduct.starTranspose A)).SmallSetExpanding
        expansionRadius expansionNumerator expansionDenominator) :
    expansionNumerator * min (q * dualDistanceLowerBound) threshold ≤
      max (2 * expansionNumerator) (4 * expansionDenominator) *
        HammingWeight z := by
  let Adual := LiftedProduct.starTranspose A
  let dualZ := LiftedProductDuality.swapWord z
  have hDualWeight : HammingWeight dualZ = HammingWeight z :=
    LiftedProductDuality.HammingWeight_swapWord z
  have hzDual : dualZ ∈ (LiftedProduct.chainComplex
      (Cyclic.liftedProductData Adual
        (Cyclic.cyclicGenerator q)⁻¹)).middleCycleCode.carrier :=
    dualCycle_mem_invGenerator_middleCycleCode q A z hz
  have hzDualNotBoundary : dualZ ∉ (LiftedProduct.chainComplex
      (Cyclic.liftedProductData Adual
        (Cyclic.cyclicGenerator q)⁻¹)).middleBoundaryCode.carrier :=
    dualCycle_not_invGenerator_boundary_of_horizontalCohomologyProjection_ne_zero
      q A z hz hProjected
  let dualClass :=
    (LiftedProduct.chainComplex
      (Cyclic.liftedProductData Adual
        (Cyclic.cyclicGenerator q)⁻¹)).middleBoundaryInCycles.mkQ
          ⟨dualZ, hzDual⟩
  by_cases hDualProjected :
      HorizontalSubsystem.horizontalHomologyProjection Adual
        (Cyclic.cyclicGenerator q)⁻¹ dualClass ≠ 0
  · have hCaseOne :=
      nonzero_horizontalClass_caseOne_invGenerator_weight_bound_distanceLowerBound
        q Adual dualZ hzDual hDualMinimum hDualDistanceLower hDualProjected
          expansionNumerator expansionDenominator hDualDistanceLowerPositive
            hCaseOneExpansion
    calc
      expansionNumerator * min (q * dualDistanceLowerBound) threshold ≤
          expansionNumerator * (q * dualDistanceLowerBound) :=
        Nat.mul_le_mul_left expansionNumerator (Nat.min_le_left _ _)
      _ ≤ max (2 * expansionNumerator) (4 * expansionDenominator) *
          HammingWeight dualZ := hCaseOne
      _ = max (2 * expansionNumerator) (4 * expansionDenominator) *
          HammingWeight z := by rw [hDualWeight]
  · have hDualProjectedZero :
        HorizontalSubsystem.horizontalHomologyProjection Adual
          (Cyclic.cyclicGenerator q)⁻¹ dualClass = 0 :=
      not_ne_iff.mp hDualProjected
    have hCaseTwo := zero_horizontalClass_caseTwo_invGenerator_weight_bound
      q hq Adual dualZ hzDual hzDualNotBoundary hDualProjectedZero
        w threshold expansionRadius expansionNumerator expansionDenominator
          hw hthreshold hThresholdScale hColumnWeight hRadius hCaseTwoExpansion
    calc
      expansionNumerator * min (q * dualDistanceLowerBound) threshold ≤
          expansionNumerator * threshold :=
        Nat.mul_le_mul_left expansionNumerator (Nat.min_le_right _ _)
      _ ≤ max (2 * expansionNumerator) (4 * expansionDenominator) *
          HammingWeight dualZ := hCaseTwo
      _ = max (2 * expansionNumerator) (4 * expansionDenominator) *
          HammingWeight z := by rw [hDualWeight]
end QEC.Coding.BalancedProduct.PKDistance
