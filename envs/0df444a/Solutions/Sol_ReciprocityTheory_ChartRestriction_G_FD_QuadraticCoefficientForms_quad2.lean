-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.QuadraticCoefficientForms.quad2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:05:49.97647+00:00
-- url     : https://prove2.me/submissions/b73a411b-bc4b-449e-bb47-6a691eaba4ff

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowIsotropicPairs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_PackingSeparation
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_QuadraticCoefficientForms
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_cc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_eq_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_intCast
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_inv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_natCast
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_neg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_sub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_add
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_cc
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_eq_zero
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_intCast
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_inv
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_mul
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_natCast
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_neg
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_one
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_sub
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_zero



set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.QuadraticCoefficientForms
open NumberField Complex ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate Classical
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace ReciprocityTheory.ChartRestriction.G.FD.QuadraticCoefficientForms
theorem _root_.solution (M : Matrix (Fin 2) (Fin 2) ℂ) (hM : M.IsHermitian) (a : Fin 2 → ℂ) :
    M.det.re * Complex.normSq (a 1) ≤ (M 0 0).re * (∑ i, ∑ k, M i k * a i * conj (a k)).re := by
  have h00 : (M 0 0).im = 0 := by
    have := hM.apply 0 0
    rw [Complex.star_def] at this
    exact Complex.conj_eq_iff_im.mp this
  have h11 : (M 1 1).im = 0 := by
    have := hM.apply 1 1
    rw [Complex.star_def] at this
    exact Complex.conj_eq_iff_im.mp this
  have h10 : M 1 0 = conj (M 0 1) := by
    have := hM.apply 1 0
    rw [Complex.star_def] at this
    exact this.symm
  simp only [Matrix.det_fin_two, Fin.sum_univ_two, h10, Complex.sub_re, Complex.add_re,
    Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.normSq_apply, h00, h11]
  nlinarith [sq_nonneg ((M 0 0).re * (a 0).re + (M 0 1).re * (a 1).re + (M 0 1).im * (a 1).im),
    sq_nonneg ((M 0 0).re * (a 0).im + (M 0 1).re * (a 1).im - (M 0 1).im * (a 1).re)]
end ReciprocityTheory.ChartRestriction.G.FD.QuadraticCoefficientForms
