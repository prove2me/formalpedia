-- Prove2me | solution 1 for ReciprocityTheory.AnForm.leviC_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:07:45.07542+00:00
-- url     : https://prove2.me/submissions/0bc3d4b9-b07f-44fb-8303-f05791f3f1bd

import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_MaDensCompEqZeroOfRankLt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm
open Complex Filter Topology
open scoped Matrix
noncomputable section
namespace ReciprocityTheory.AnForm
theorem _root_.solution {e : ℕ} (H : (Fin e → ℂ) →L[ℝ] (Fin e → ℂ) →L[ℝ] ℝ) (c : ℂ) (a b : Fin e → ℂ) :
    leviC H (c • a) b = c * leviC H a b := by
  have hc : c • a = (c.re : ℝ) • a + (c.im : ℝ) • (I • a) := by
    funext k
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Complex.real_smul]
    conv_lhs => rw [← Complex.re_add_im c]
    ring
  have hc' : I • (c • a) = (c.re : ℝ) • (I • a) + (-c.im : ℝ) • a := by
    funext k
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Complex.real_smul, Complex.ofReal_neg]
    conv_lhs => rw [← Complex.re_add_im c]
    linear_combination (↑c.im * a k) * Complex.I_sq
  unfold leviC
  rw [hc', hc]
  simp only [map_add, map_smul, ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_smul',
    Pi.smul_apply, smul_eq_mul]
  push_cast
  conv_rhs => rw [← Complex.re_add_im c]
  ring_nf
  simp only [Complex.I_sq]
  ring
end ReciprocityTheory.AnForm
