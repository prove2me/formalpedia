-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsCuspHorocycleCircle_norm_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:07:41.685641+00:00
-- url     : https://prove2.me/submissions/2fae7bf4-482e-4f4e-a651-65d901bfd518

import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.NumberTheory.ModularForms.Bounds
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspHorocycle
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHorocyclePoint_im
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCuspHorocycleCircle_coe
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHorocyclePoint_im

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology MeasureTheory Asymptotics
open scoped MatrixGroups UpperHalfPlane ModularForm
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) :
    ∃ C : ℝ, 0≤C ∧ ∀ (y : ℝ) (_hy : 0<y) (x : AddCircle (1:ℝ)),
      ‖lpsCuspHorocycleCircle N f y x‖≤C/y := by
  obtain ⟨C,hC⟩ := CuspFormClass.exists_bound f
  have hb (τ : ℍ) : ‖f τ‖≤C/τ.im := by simpa using hC τ
  have hC0 : 0≤C := by
    have h := hb (lpsHorocyclePoint 1 (by norm_num) 0)
    simp only [lpsHorocyclePoint_im,div_one] at h
    exact (norm_nonneg _).trans h
  refine ⟨C,hC0,fun y hy x => ?_⟩
  induction x using QuotientAddGroup.induction_on with | H x =>
    rw [lpsCuspHorocycleCircle_coe N f y hy]
    exact hb _
end QEC.Coding.TannerLiftedProduct
