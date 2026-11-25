-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.QuadraticOffDiagonalBounds.offdiag_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:00:18.766492+00:00
-- url     : https://prove2.me/submissions/969791b2-7ceb-4819-8ec9-57d6d11bbfb5

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_UnipotentCoefficientShift
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_QuadraticOffDiagonalBounds
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_QuadraticOffDiagonalBounds_quad_nonneg
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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open ReciprocityTheory.ChartRestriction.G.FD.QuadraticOffDiagonalBounds
open NumberField Complex
open scoped ComplexConjugate ComplexOrder
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace ReciprocityTheory.ChartRestriction.G.FD.QuadraticOffDiagonalBounds
theorem _root_.solution {M : Fin 2 → Fin 2 → ℂ} (hM : (Matrix.of M).PosSemidef)
    (h10 : M 1 0 = conj (M 0 1)) : 2 * ‖M 0 1‖ ≤ (M 0 0).re + (M 1 1).re := by
  have d0 := quad_nonneg hM ![1, 0]
  have d1 := quad_nonneg hM ![0, 1]
  simp [Fin.sum_univ_two] at d0 d1
  rcases eq_or_ne (M 0 1) 0 with h0 | h0
  · rw [h0, norm_zero, mul_zero]
    linarith
  · have hn : 0 < ‖M 0 1‖ := norm_pos_iff.mpr h0
    have hs : M 0 1 * conj (M 0 1) = ((‖M 0 1‖ : ℝ) : ℂ) ^ 2 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_pow]
    have h := quad_nonneg hM ![conj (M 0 1), -((‖M 0 1‖ : ℝ) : ℂ)]
    have e : (∑ i, ∑ k, M i k * ![conj (M 0 1), -((‖M 0 1‖ : ℝ) : ℂ)] i *
        conj (![conj (M 0 1), -((‖M 0 1‖ : ℝ) : ℂ)] k)) =
        ((‖M 0 1‖ ^ 2 : ℝ) : ℂ) * (M 0 0 + M 1 1) - ((2 * ‖M 0 1‖ ^ 3 : ℝ) : ℂ) := by
      simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        map_neg, Complex.conj_conj, Complex.conj_ofReal, h10]
      push_cast
      linear_combination (M 0 0 - 2 * ((‖M 0 1‖ : ℝ) : ℂ)) * hs
    rw [e] at h
    have h' := h
    simp only [Complex.zero_re, Complex.sub_re, Complex.re_ofReal_mul, Complex.add_re,
      Complex.ofReal_re] at h'
    by_contra hlt
    push_neg at hlt
    have hm := mul_lt_mul_of_pos_left hlt (pow_pos hn 2)
    nlinarith
end ReciprocityTheory.ChartRestriction.G.FD.QuadraticOffDiagonalBounds
