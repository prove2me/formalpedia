-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsCuspHorocycleTerm_norm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:15:41.989994+00:00
-- url     : https://prove2.me/submissions/bbd47649-f968-4da5-89b5-913ed37323be

import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.NumberTheory.ModularForms.Bounds
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspHorocycle

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology MeasureTheory Asymptotics
open scoped MatrixGroups UpperHalfPlane ModularForm
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (y : ℝ) (n : ℕ) (x : AddCircle (1:ℝ)) :
    ‖lpsCuspHorocycleTerm N f y n x‖=
      ‖PowerSeries.coeff n (UpperHalfPlane.qExpansion 1 f)‖*(Real.exp (-2*Real.pi*y))^n := by
  unfold lpsCuspHorocycleTerm
  rw [norm_mul,norm_mul,norm_pow,fourier_apply,Circle.norm_coe,mul_one,
    Complex.norm_real,Real.norm_eq_abs,Real.abs_exp]
end QEC.Coding.TannerLiftedProduct
