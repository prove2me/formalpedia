-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsCuspHorocycle_parseval
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:45:36.285285+00:00
-- url     : https://prove2.me/submissions/e830c80c-634c-44a8-8cf7-ccf299cd83e2

import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.NumberTheory.ModularForms.Bounds
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspHorocycle
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCuspHorocycleCircle_parseval_nat
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCuspHorocycle_integral

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology MeasureTheory Asymptotics
open scoped MatrixGroups UpperHalfPlane ModularForm
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (y : ℝ) (hy : 0<y) :
    HasSum (fun n : ℕ => ‖PowerSeries.coeff n (UpperHalfPlane.qExpansion 1 f)‖^2*
      (Real.exp (-2*Real.pi*y))^(2*n))
      (∫ x in (0:ℝ)..1, ‖f (lpsHorocyclePoint y hy x)‖^2) := by
  rw [←lpsCuspHorocycle_integral N f y hy]
  exact lpsCuspHorocycleCircle_parseval_nat N f y hy
end QEC.Coding.TannerLiftedProduct
