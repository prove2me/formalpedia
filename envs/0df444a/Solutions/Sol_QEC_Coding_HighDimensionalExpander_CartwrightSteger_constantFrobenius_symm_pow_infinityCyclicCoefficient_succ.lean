-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.constantFrobenius_symm_pow_infinityCyclicCoefficient_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T13:21:36.107445+00:00
-- url     : https://prove2.me/submissions/3610b732-1bea-48f8-ad69-de0da54d3074

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingStabilizer
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_InfinityAction
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_constantFrobenius_pow_infinityCyclicCoefficient
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_constantFrobenius_symm_pow_succ_apply

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) (u : (ConstantExtension P r)ˣ)
    (k i : ℕ) :
    (constantFrobenius P r).symm
        ((constantFrobenius P r ^ k)
          (infinityCyclicCoefficient P r u (i + 1) :
            ConstantExtension P r)) =
      (constantFrobenius P r).symm
          ((constantFrobenius P r ^ k) (u : ConstantExtension P r)) *
        ((constantFrobenius P r ^ (k + i))
          (u : ConstantExtension P r))⁻¹ := by
  rw [constantFrobenius_pow_infinityCyclicCoefficient]
  rw [map_mul, map_inv₀]
  have hexponent : k + (i + 1) = (k + i) + 1 := by omega
  rw [hexponent, constantFrobenius_symm_pow_succ_apply]
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
