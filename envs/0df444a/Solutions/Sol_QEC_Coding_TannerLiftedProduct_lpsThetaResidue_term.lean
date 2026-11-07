-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsThetaResidue_term
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:42:31.578346+00:00
-- url     : https://prove2.me/submissions/a1ae0176-ed4b-4bda-bd92-6e4c2bbddd2c

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaS
import Mathlib.NumberTheory.ModularForms.JacobiTheta.Bounds
import Mathlib.Logic.Equiv.Fin.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCharacteristics

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Real Filter Topology
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (a k : ℤ) (c : ℕ) [NeZero c] (r : Fin c) (z : ℂ) :
    Complex.exp ((Real.pi:ℂ)*Complex.I*((k:ℂ)*(c:ℂ)+(r.val:ℂ))^2*(z+2*(a:ℂ)/(c:ℂ))) =
      lpsQuadraticPhase a c r *
        Complex.exp ((Real.pi:ℂ)*Complex.I*((k:ℂ)+(r.val:ℂ)/(c:ℂ))^2*((c:ℂ)^2*z)) := by
  have hc : (c:ℂ)≠0 := by exact_mod_cast NeZero.ne c
  have he : (Real.pi:ℂ)*Complex.I*((k:ℂ)*(c:ℂ)+(r.val:ℂ))^2*(z+2*(a:ℂ)/(c:ℂ)) =
      2*(Real.pi:ℂ)*Complex.I*(a:ℂ)*(r.val:ℂ)^2/(c:ℂ) +
      (Real.pi:ℂ)*Complex.I*((k:ℂ)+(r.val:ℂ)/(c:ℂ))^2*((c:ℂ)^2*z) +
      ((a*(k^2*(c:ℤ)+2*k*(r.val:ℤ)) : ℤ):ℂ)*(2*(Real.pi:ℂ)*Complex.I) := by
    push_cast
    field_simp [hc]
    ring
  rw [he,Complex.exp_add,Complex.exp_int_mul_two_pi_mul_I,mul_one,Complex.exp_add]
  rfl
end QEC.Coding.TannerLiftedProduct
