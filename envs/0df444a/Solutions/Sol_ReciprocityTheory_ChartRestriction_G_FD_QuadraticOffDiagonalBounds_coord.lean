-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.QuadraticOffDiagonalBounds.coord
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:59:55.420266+00:00
-- url     : https://prove2.me/submissions/30c5ba49-e66f-4bbb-b20e-59f2af64b175

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_UnipotentCoefficientShift
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_QuadraticOffDiagonalBounds
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
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_UnipotentCoefficientShift_Hf_conj
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


section
namespace ReciprocityTheory.ChartRestriction.G.FD
namespace QuadraticOffDiagonalBounds
open NumberField Complex
open scoped ComplexConjugate ComplexOrder
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
variable {r : ℕ} {X : Data E r}
private theorem Hf_smul_add_smul_right (z : Frame X.Ψ r) (τ : X.Ψ) (u v w : Fin r → ℂ) (a b : ℂ) :
    X.Hf z τ u (a • v + b • w) = conj a * X.Hf z τ u v + conj b * X.Hf z τ u w := by
  simp only [Data.Hf, hermC, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, map_mul]
  ring
end QuadraticOffDiagonalBounds
end ReciprocityTheory.ChartRestriction.G.FD
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open ReciprocityTheory.ChartRestriction.G.FD.QuadraticOffDiagonalBounds
open NumberField Complex
open scoped ComplexConjugate ComplexOrder
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
variable {r : ℕ} {X : Data E r}
namespace ReciprocityTheory.ChartRestriction.G.FD.QuadraticOffDiagonalBounds
theorem _root_.solution {z : Frame X.Ψ r} (hz : z ∈ X.dom) (τ : X.Ψ) (f1 f2 e : Fin r → ℂ) (a0 a1 : ℂ)
    (c : ℝ) (he : e = a0 • f1 + a1 • f2) (h1 : c * (X.Hf z τ f1 f1).re = 1)
    (h2 : X.Hf z τ e f1 = 0) (h3 : c * (X.Hf z τ e e).re = 1) :
    ∃ p q : ℂ, q * a0 + p = 0 ∧ q * a1 = 1 ∧ ‖p‖ ^ 2 + ‖q‖ ^ 2 = c * (X.Hf z τ f2 f2).re := by
  have hc : ∀ u w, conj (X.Hf z τ u w) = X.Hf z τ w u := fun u w => UnipotentCoefficientShift.Hf_conj hz τ u w
  have hL : ∀ w, X.Hf z τ e w = a0 * X.Hf z τ f1 w + a1 * X.Hf z τ f2 w := by
    intro w
    rw [← hc w e, he, Hf_smul_add_smul_right, map_add, map_mul, map_mul, Complex.conj_conj, Complex.conj_conj,
      hc, hc]
  have h2' : a0 * X.Hf z τ f1 f1 + a1 * X.Hf z τ f2 f1 = 0 := by rw [← hL, h2]
  have hee : X.Hf z τ e e = conj a0 * X.Hf z τ e f1 + conj a1 * X.Hf z τ e f2 := by
    have := Hf_smul_add_smul_right z τ e f1 f2 a0 a1
    rwa [← he] at this
  rw [h2, mul_zero, zero_add, hL f2, ← hc f2 f1] at hee
  have hA : conj (X.Hf z τ f1 f1) = X.Hf z τ f1 f1 := hc f1 f1
  have hD : conj (X.Hf z τ f2 f2) = X.Hf z τ f2 f2 := hc f2 f2
  have hB : conj a1 * conj (X.Hf z τ f2 f1) = -(conj a0 * X.Hf z τ f1 f1) := by
    rw [← map_mul, show a1 * X.Hf z τ f2 f1 = -(a0 * X.Hf z τ f1 f1) by linear_combination h2',
      map_neg, map_mul, hA]
  have hee2 : X.Hf z τ e e = -(a0 * conj a0) * X.Hf z τ f1 f1 + (a1 * conj a1) * X.Hf z τ f2 f2 := by
    rw [hee]
    linear_combination a0 * hB
  have hAr : ((X.Hf z τ f1 f1).re : ℂ) = X.Hf z τ f1 f1 := Complex.conj_eq_iff_re.mp hA
  have hDr : ((X.Hf z τ f2 f2).re : ℂ) = X.Hf z τ f2 f2 := Complex.conj_eq_iff_re.mp hD
  have hre : (X.Hf z τ e e).re =
      -(‖a0‖ ^ 2) * (X.Hf z τ f1 f1).re + ‖a1‖ ^ 2 * (X.Hf z τ f2 f2).re := by
    rw [hee2, ← hAr, ← hDr, Complex.mul_conj, Complex.mul_conj, Complex.normSq_eq_norm_sq,
      Complex.normSq_eq_norm_sq]
    simp only [Complex.add_re, Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.ofReal_re,
      Complex.ofReal_im]
    ring
  rw [hre] at h3
  have key : ‖a1‖ ^ 2 * (c * (X.Hf z τ f2 f2).re) = 1 + ‖a0‖ ^ 2 := by
    linear_combination h3 + ‖a0‖ ^ 2 * h1
  have ha1 : a1 ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at key
    nlinarith [sq_nonneg ‖a0‖]
  have hn : 0 < ‖a1‖ := norm_pos_iff.mpr ha1
  have hcd : c * (X.Hf z τ f2 f2).re = (1 + ‖a0‖ ^ 2) / ‖a1‖ ^ 2 := by
    rw [eq_div_iff (by positivity)]
    linear_combination key
  refine ⟨-a0 * a1⁻¹, a1⁻¹, by ring, inv_mul_cancel₀ ha1, ?_⟩
  rw [hcd, norm_mul, norm_neg, norm_inv]
  field_simp
  ring
end ReciprocityTheory.ChartRestriction.G.FD.QuadraticOffDiagonalBounds
