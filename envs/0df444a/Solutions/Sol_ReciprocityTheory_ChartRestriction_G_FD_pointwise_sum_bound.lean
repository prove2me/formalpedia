-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.pointwise_sum_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:00:41.104106+00:00
-- url     : https://prove2.me/submissions/1e64bcec-2b8f-46a6-959a-371b18e32a41

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_UnipotentVectorEqSmulComponent
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ShortVectorBoundOfCoefficientBounds
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_pointNorm_eq_norm_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_pointNorm_nonneg
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
open NumberField Complex
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace ReciprocityTheory.ChartRestriction.G.FD
theorem _root_.solution {r : ℕ} (X : Data E r) (la : Wt X.Ψ r) (Q : Frame X.Ψ r → ℂ)
    (F : (X.Ψ → Fin 2 → Fin 2 → ℂ) → Frame X.Ψ r → ℂ) (T : (X.Ψ → Fin 2 → Fin 2 → ℂ) → ℝ)
    (w S1 : ℝ) (hS10 : 0 ≤ S1) (z0 : Frame X.Ψ r)
    (hexp : ∀ z ∈ X.dom, Summable (fun χ => ‖F χ z‖) → HasSum (fun χ => F χ z) (Q z))
    (hpt : ∀ χ, ∀ z ∈ X.dom, X.SameFlag z0 z →
      X.pnorm la (F χ) z ≤ 2 ^ (w / 2) * Real.exp (-Real.pi * T χ) * S1)
    (hsum : Summable (fun j : ↥{χ | ∃ y ∈ X.dom, F χ y ≠ 0} => Real.exp (-Real.pi * T j.1))) :
    ∀ z ∈ X.dom, X.SameFlag z0 z → X.pnorm la Q z ≤
      2 ^ (w / 2) * (∑' j : ↥{χ | ∃ y ∈ X.dom, F χ y ≠ 0}, Real.exp (-Real.pi * T j.1)) * S1 := by
  intro z hz hfl
  have hN := X.pointNorm_nonneg la (fun _ => (1 : ℂ)) z
  have hC : 0 ≤ (2 : ℝ) ^ (w / 2) := by positivity
  have htn : 0 ≤ ∑' j : ↥{χ | ∃ y ∈ X.dom, F χ y ≠ 0}, Real.exp (-Real.pi * T j.1) :=
    tsum_nonneg fun _ => (Real.exp_pos _).le
  rw [X.pointNorm_eq_norm_mul la Q z]
  rcases hN.eq_or_lt with hN0 | hNpos
  · rw [← hN0, mul_zero]
    exact mul_nonneg (mul_nonneg hC htn) hS10
  have hpt' : ∀ χ, ‖F χ z‖ * X.pnorm la (fun _ => (1 : ℂ)) z ≤
      2 ^ (w / 2) * Real.exp (-Real.pi * T χ) * S1 := fun χ => by
    rw [← X.pointNorm_eq_norm_mul la (F χ) z]; exact hpt χ z hz hfl
  have hb : ∀ χ, ‖F χ z‖ ≤
      2 ^ (w / 2) * S1 / X.pnorm la (fun _ => (1 : ℂ)) z * Real.exp (-Real.pi * T χ) := by
    intro χ
    rw [div_mul_eq_mul_div, le_div_iff₀ hNpos]
    linarith [hpt' χ]
  have hzero : ∀ χ, χ ∉ {χ | ∃ y ∈ X.dom, F χ y ≠ 0} → F χ z = 0 := fun χ hχ => by
    by_contra h; exact hχ ⟨z, hz, h⟩
  have hsupp : Function.support (fun χ => ‖F χ z‖) ⊆ {χ | ∃ y ∈ X.dom, F χ y ≠ 0} := by
    intro χ hχ
    by_contra h
    exact hχ (by simp only [hzero χ h, norm_zero])
  have hsumS : Summable (fun j : ↥{χ | ∃ y ∈ X.dom, F χ y ≠ 0} => ‖F j.1 z‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun j => hb j.1) (hsum.mul_left _)
  have hsumAll : Summable (fun χ => ‖F χ z‖) := by
    refine (Function.Injective.summable_iff Subtype.val_injective fun χ hχ => ?_).1 hsumS
    rw [norm_eq_zero]
    exact hzero χ fun h => hχ ⟨⟨χ, h⟩, rfl⟩
  have hQ := hexp z hz hsumAll
  have hnorm : ‖Q z‖ ≤ ∑' χ, ‖F χ z‖ := by
    rw [← hQ.tsum_eq]; exact norm_tsum_le_tsum_norm hsumAll
  rw [← tsum_subtype_eq_of_support_subset hsupp] at hnorm
  have hsum2 : Summable (fun j : ↥{χ | ∃ y ∈ X.dom, F χ y ≠ 0} =>
      2 ^ (w / 2) * S1 / X.pnorm la (fun _ => (1 : ℂ)) z * Real.exp (-Real.pi * T j.1)) :=
    hsum.mul_left _
  have hle : ∑' j : ↥{χ | ∃ y ∈ X.dom, F χ y ≠ 0}, ‖F j.1 z‖ ≤
      2 ^ (w / 2) * S1 / X.pnorm la (fun _ => (1 : ℂ)) z *
        ∑' j : ↥{χ | ∃ y ∈ X.dom, F χ y ≠ 0}, Real.exp (-Real.pi * T j.1) := by
    rw [← tsum_mul_left]
    exact hsumS.tsum_le_tsum (fun j => hb j.1) hsum2
  have hm := mul_le_mul_of_nonneg_right (hnorm.trans hle) hN
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, mul_div_assoc, div_self hNpos.ne', mul_one] at hm
  linarith
end ReciprocityTheory.ChartRestriction.G.FD
