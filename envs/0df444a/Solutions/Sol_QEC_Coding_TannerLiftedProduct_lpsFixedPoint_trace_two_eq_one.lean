-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsFixedPoint_trace_two_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:46:27.04639+00:00
-- url     : https://prove2.me/submissions/b82aa9af-2a1f-46be-8007-e56906f80e94

import Mathlib.Analysis.Complex.UpperHalfPlane.FixedPoints
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGamma0Stabilizers
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsFixedPoint_trace_identity

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Matrix Filter Topology
open scoped MatrixGroups UpperHalfPlane
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (g : GL (Fin 2) ℝ) (hdet : g.val.det=1)
    (htrace : g.val.trace=2) (τ : ℍ) (hfix : g • τ=τ) : g=1 := by
  have hi := lpsFixedPoint_trace_identity g hdet τ hfix
  rw [htrace] at hi
  have hz : ((g 1 0)*τ.im)^2=0 := by nlinarith [hi]
  have hm := sq_eq_zero_iff.mp hz
  have hc : g 1 0=0 := (mul_eq_zero.mp hm).resolve_right τ.im_ne_zero
  have ht := htrace
  rw [Matrix.trace_fin_two] at ht
  have hd := hdet
  rw [Matrix.det_fin_two,hc,mul_zero,sub_zero] at hd
  have hdd : g 1 1=2-g 0 0 := by linarith [ht]
  rw [hdd] at hd
  have ha0 : (g 0 0-1)^2=0 := by nlinarith [hd]
  have ha : g 0 0=1 := sub_eq_zero.mp (sq_eq_zero_iff.mp ha0)
  have hd1 : g 1 1=1 := by linarith [ht]
  have hq := (UpperHalfPlane.gl_smul_eq_self_iff_quadratic (by rw [hdet];norm_num)).mp hfix
  simp only [hc,ha,hd1,Complex.ofReal_zero,Complex.ofReal_one,
    zero_mul,sub_self,zero_add,add_zero,neg_eq_zero] at hq
  have hb : g 0 1=0 := by exact_mod_cast hq
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ha,hb,hc,hd1]
end QEC.Coding.TannerLiftedProduct
