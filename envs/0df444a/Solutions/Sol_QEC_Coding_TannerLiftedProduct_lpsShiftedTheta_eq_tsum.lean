-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsShiftedTheta_eq_tsum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:42:22.826273+00:00
-- url     : https://prove2.me/submissions/1d9151ae-bd54-47a8-b200-fa7b661b3d3e

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaS
import Mathlib.NumberTheory.ModularForms.JacobiTheta.Bounds
import Mathlib.Logic.Equiv.Fin.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCharacteristics

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Real Filter Topology
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (a z : ℂ) : lpsShiftedTheta a z =
    ∑' n : ℤ, Complex.exp ((Real.pi:ℂ)*Complex.I*((n:ℂ)+a)^2*z) := by
  unfold lpsShiftedTheta jacobiTheta₂
  rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  rw [jacobiTheta₂_term,← Complex.exp_add]
  congr 1
  ring
end QEC.Coding.TannerLiftedProduct
