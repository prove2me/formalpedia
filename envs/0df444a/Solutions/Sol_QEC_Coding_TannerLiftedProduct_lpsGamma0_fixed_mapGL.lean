-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsGamma0_fixed_mapGL
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:48:38.63665+00:00
-- url     : https://prove2.me/submissions/19811825-b233-4be3-a18b-5d1666f7441b

import Mathlib.Analysis.Complex.UpperHalfPlane.FixedPoints
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGamma0Stabilizers
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsFixedPoint_trace_two_eq_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsGamma0_fixed_trace

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Matrix Filter Topology
open scoped MatrixGroups UpperHalfPlane
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) (hN : 4∣N) (γ : SL(2,ℤ))
    (hγ : γ∈CongruenceSubgroup.Gamma0 N) (τ : ℍ)
    (hfix : Matrix.SpecialLinearGroup.mapGL ℝ γ • τ=τ) :
    Matrix.SpecialLinearGroup.mapGL ℝ γ=1 ∨
      Matrix.SpecialLinearGroup.mapGL ℝ γ= -1 := by
  let g := Matrix.SpecialLinearGroup.mapGL ℝ γ
  have hd : g.val.det=1 := by
    simp only [g,← Matrix.GeneralLinearGroup.val_det_apply,Matrix.SpecialLinearGroup.det_mapGL,
      Units.val_one]
  have he : g.val.trace=((γ:Matrix (Fin 2) (Fin 2) ℤ).trace:ℝ) := by
    simp [g,Matrix.SpecialLinearGroup.mapGL_coe_matrix,Matrix.trace_fin_two]
  rcases lpsGamma0_fixed_trace N hN γ hγ τ hfix with hp|hm
  · left
    apply lpsFixedPoint_trace_two_eq_one g hd _ τ hfix
    rw [he,hp]; norm_num
  · right
    have hdn : (-g).val.det=1 := by simpa [Matrix.det_neg] using hd
    have htn : (-g).val.trace=2 := by simp [Matrix.trace_neg,he,hm]
    have hfn : -g • τ=τ := by simpa only [UpperHalfPlane.neg_smul] using hfix
    have hi := lpsFixedPoint_trace_two_eq_one (-g) hdn htn τ hfn
    exact neg_injective (by simpa using hi)
end QEC.Coding.TannerLiftedProduct
