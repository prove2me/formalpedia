-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsCuspHorocycle_weighted_square_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:12:48.340634+00:00
-- url     : https://prove2.me/submissions/2bc2b18c-6509-49fa-9296-f91f956ba7fb

import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.NumberTheory.ModularForms.Bounds
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspHorocycle
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCuspHorocycleCircle_parseval_nat
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCuspHorocycleCircle_norm_bound
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCuspHorocycle_integral_bound_of_norm_bound

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology MeasureTheory Asymptotics
open scoped MatrixGroups UpperHalfPlane ModularForm
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) :
    ∃ C : ℝ, 0≤C ∧ ∀ (y : ℝ) (_hy : 0<y),
      (∑' n : ℕ, ‖PowerSeries.coeff n (UpperHalfPlane.qExpansion 1 f)‖^2*
        (Real.exp (-2*Real.pi*y))^(2*n))≤(C/y)^2 := by
  obtain ⟨C,hC,hb⟩ := lpsCuspHorocycleCircle_norm_bound N f
  refine ⟨C,hC,fun y hy => ?_⟩
  rw [(lpsCuspHorocycleCircle_parseval_nat N f y hy).tsum_eq]
  exact lpsCuspHorocycle_integral_bound_of_norm_bound N f C y hy (hb y hy)
end QEC.Coding.TannerLiftedProduct
