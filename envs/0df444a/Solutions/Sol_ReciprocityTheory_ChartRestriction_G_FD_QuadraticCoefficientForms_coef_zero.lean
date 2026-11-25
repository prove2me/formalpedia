-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.QuadraticCoefficientForms.coef_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:59:47.988071+00:00
-- url     : https://prove2.me/submissions/9a7a3989-3f42-47ab-b09f-9e420bc344ed

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
theorem _root_.solution {r : ℕ} {ξ x : Fin r → E} (hξ0 : ξ ≠ 0) (hne : ∀ e : E, x ≠ e • ξ)
    (τ : E →+* ℂ) (p q : ℂ) (h : p • Data.emb τ ξ + q • Data.emb τ x = 0) : q = 0 := by
  obtain ⟨a, ha⟩ : ∃ a, ξ a ≠ 0 := by
    by_contra h0
    push_neg at h0
    exact hξ0 (funext h0)
  obtain ⟨b, hb⟩ : ∃ b, x b ≠ (x a / ξ a) * ξ b := by
    by_contra h0
    push_neg at h0
    exact hne (x a / ξ a) (funext fun b => by rw [Pi.smul_apply, smul_eq_mul, h0 b])
  have hm : ξ a * x b - ξ b * x a ≠ 0 := by
    intro h0
    apply hb
    rw [div_mul_eq_mul_div, eq_div_iff ha]
    linear_combination h0
  have h1 := congrFun h a
  have h2 := congrFun h b
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, Data.emb] at h1 h2
  have hτ : τ (ξ a * x b - ξ b * x a) ≠ 0 := (map_ne_zero τ).2 hm
  rw [map_sub, map_mul, map_mul] at hτ
  have h3 : q * (τ (ξ a) * τ (x b) - τ (ξ b) * τ (x a)) = 0 := by
    linear_combination τ (ξ a) * h2 - τ (ξ b) * h1
  exact (mul_eq_zero.1 h3).resolve_right hτ
end ReciprocityTheory.ChartRestriction.G.FD.QuadraticCoefficientForms
