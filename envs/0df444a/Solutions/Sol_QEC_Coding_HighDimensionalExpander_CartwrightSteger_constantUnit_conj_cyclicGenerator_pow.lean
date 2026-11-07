-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.constantUnit_conj_cyclicGenerator_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T13:23:27.156193+00:00
-- url     : https://prove2.me/submissions/69542456-9820-41da-8ca2-c9c4d3bd550c

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingStabilizer
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_InfinityAction
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cyclicGenerator_pow_conj_constantUnit

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) (u : (ConstantExtension P r)ˣ) (k : ℕ) :
    constantUnitMatrix P r u * cyclicGenerator P r ^ k *
        (constantUnitMatrix P r u)⁻¹ =
      constantUnitMatrix P r (infinityCyclicCoefficient P r u k) *
        cyclicGenerator P r ^ k := by
  have huInv := cyclicGenerator_pow_conj_constantUnit P r k u⁻¹
  have hconstantInv :
      (constantUnitMatrix P r u)⁻¹ = constantUnitMatrix P r u⁻¹ := by
    change (constantUnitMatrixHom P r u)⁻¹ = constantUnitMatrixHom P r u⁻¹
    rw [map_inv]
  have hFrobeniusInv :
      (constantFrobeniusUnitEquiv P r ^ k) u⁻¹ =
        ((constantFrobeniusUnitEquiv P r ^ k) u)⁻¹ := by
    exact map_inv _ _
  have hconstantMul
      (a b : (ConstantExtension P r)ˣ) :
      constantUnitMatrix P r a * constantUnitMatrix P r b =
        constantUnitMatrix P r (a * b) := by
    change constantUnitMatrixHom P r a * constantUnitMatrixHom P r b =
      constantUnitMatrixHom P r (a * b)
    rw [map_mul]
  calc
    constantUnitMatrix P r u * cyclicGenerator P r ^ k *
          (constantUnitMatrix P r u)⁻¹ =
        constantUnitMatrix P r u *
          (cyclicGenerator P r ^ k * constantUnitMatrix P r u⁻¹ *
            (cyclicGenerator P r ^ k)⁻¹) *
          cyclicGenerator P r ^ k := by
            rw [hconstantInv]
            group
    _ = constantUnitMatrix P r u *
          constantUnitMatrix P r
            ((constantFrobeniusUnitEquiv P r ^ k) u⁻¹) *
          cyclicGenerator P r ^ k := by rw [huInv]
    _ = constantUnitMatrix P r (infinityCyclicCoefficient P r u k) *
          cyclicGenerator P r ^ k := by
            rw [hFrobeniusInv, infinityCyclicCoefficient, hconstantMul]
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
