-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.constantFrobenius_pow_infinityCyclicCoefficient
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T13:04:11.485823+00:00
-- url     : https://prove2.me/submissions/e951b385-89ba-4a44-bbec-31c16406be26

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingStabilizer
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_InfinityAction
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_infinityCyclicCoefficient_coe

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) (u : (ConstantExtension P r)ˣ)
    (k i : ℕ) :
    (constantFrobenius P r ^ k)
        (infinityCyclicCoefficient P r u i : ConstantExtension P r) =
      (constantFrobenius P r ^ k) (u : ConstantExtension P r) *
        ((constantFrobenius P r ^ (k + i))
          (u : ConstantExtension P r))⁻¹ := by
  rw [infinityCyclicCoefficient_coe]
  rw [map_mul]
  rw [map_inv₀]
  have hcomp :
      (constantFrobenius P r ^ k)
          ((constantFrobenius P r ^ i) (u : ConstantExtension P r)) =
        (constantFrobenius P r ^ (k + i))
          (u : ConstantExtension P r) := by
    rw [← AlgEquiv.mul_apply, ← pow_add]
  rw [hcomp]
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
