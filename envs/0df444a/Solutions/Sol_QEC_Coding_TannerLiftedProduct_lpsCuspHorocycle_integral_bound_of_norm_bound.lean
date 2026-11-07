-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsCuspHorocycle_integral_bound_of_norm_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:10:26.310703+00:00
-- url     : https://prove2.me/submissions/d6f0b228-a064-43d3-98fb-0f6a12d4b604

import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.NumberTheory.ModularForms.Bounds
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspHorocycle
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHorocyclePoint_im
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCuspHorocycleCircle_continuous
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHorocyclePoint_im

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology MeasureTheory Asymptotics
open scoped MatrixGroups UpperHalfPlane ModularForm
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (C y : ℝ) (hy : 0<y)
    (hb : ∀ x : AddCircle (1:ℝ), ‖lpsCuspHorocycleCircle N f y x‖≤C/y) :
    (∫ x : AddCircle (1:ℝ), ‖lpsCuspHorocycleCircle N f y x‖^2 ∂AddCircle.haarAddCircle)≤
      (C/y)^2 := by
  have hi : Integrable (fun x : AddCircle (1:ℝ) => ‖lpsCuspHorocycleCircle N f y x‖^2)
      AddCircle.haarAddCircle :=
    ((lpsCuspHorocycleCircle_continuous N f y hy).norm.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have h := integral_mono hi (integrable_const ((C/y)^2)) (fun x => ?_)
  · simpa using h
  · exact pow_le_pow_left₀ (norm_nonneg _) (hb x) 2
end QEC.Coding.TannerLiftedProduct
