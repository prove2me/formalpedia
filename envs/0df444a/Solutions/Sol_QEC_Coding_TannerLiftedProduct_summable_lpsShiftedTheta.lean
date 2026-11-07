-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.summable_lpsShiftedTheta
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:43:26.945455+00:00
-- url     : https://prove2.me/submissions/e255c129-0383-445a-8a16-232c572750ea

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaS
import Mathlib.NumberTheory.ModularForms.JacobiTheta.Bounds
import Mathlib.Logic.Equiv.Fin.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCharacteristics

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Real Filter Topology
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (a z : ℂ) (hz : 0<z.im) :
    Summable (fun n : ℤ => Complex.exp ((Real.pi:ℂ)*Complex.I*((n:ℂ)+a)^2*z)) := by
  have h := (hasSum_jacobiTheta₂_term (a*z) hz).summable.mul_left
    (Complex.exp ((Real.pi:ℂ)*Complex.I*a^2*z))
  apply h.congr
  intro n
  rw [jacobiTheta₂_term,← Complex.exp_add]
  congr 1
  ring
end QEC.Coding.TannerLiftedProduct
