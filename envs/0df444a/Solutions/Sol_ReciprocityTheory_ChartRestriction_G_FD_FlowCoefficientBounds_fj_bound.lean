-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.FlowCoefficientBounds.fj_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:35:41.465542+00:00
-- url     : https://prove2.me/submissions/3bbda76f-b6d0-46c5-b7e3-c178d4400b09

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowIsotropicPairs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_M3bNormHolds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowCoefficientBounds
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FlowCoefficientBounds_nfac_pos
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FlowCoefficientBounds_norm_cexp_I
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FlowCoefficientBounds_flow_real
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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FlowCoefficientBounds
open NumberField Complex MeasureTheory ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.FD.FlowCoefficientBounds
theorem _root_.solution (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (C : ℝ)
    (hP : ∀ y ∈ X.dom, X.pnorm la P y ≤ C) {ξ : Fin r → E} (hξ : X.IsIso ξ) (ν : X.Ψ → ℝ)
    {x : Frame X.Ψ r} (hx : x ∈ X.dom) : X.pnorm la (X.fj la ξ ν P) x ≤ C := by
  have hpos := nfac_pos X hx la
  change ‖X.fj la ξ ν P x‖ * X.nfac la x ≤ C
  have hC : 0 ≤ C := le_trans (by unfold Data.pnorm; positivity) (hP x hx)
  unfold Data.fj
  split_ifs with h1 h2
  · obtain ⟨-, -, hD0, hDt⟩ := h2.choose_spec
    rw [← le_div_iff₀ hpos, norm_mul]
    have hpt : ∀ s : X.Ψ → ℝ, ‖P (X.flow ξ (fun τ => (s τ : ℂ)) x) *
        cexp (-(4 * Real.pi * I) * ∑ τ, (ν τ : ℂ) * s τ)‖ ≤ C / X.nfac la x := by
      intro s
      obtain ⟨hd, hn⟩ := flow_real X hξ hx s la
      rw [norm_mul, norm_cexp_I _ (by rw [Complex.im_sum]; simp), mul_one, le_div_iff₀ hpos, ← hn]
      exact hP _ hd
    haveI : IsFiniteMeasure (volume.restrict h2.choose) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact hDt⟩
    have hI := norm_integral_le_of_norm_le_const (μ := volume.restrict h2.choose) (ae_of_all _ hpt)
    rw [measureReal_def, Measure.restrict_apply_univ] at hI
    have hv : 0 < (volume h2.choose).toReal := ENNReal.toReal_pos hD0.ne' hDt.ne
    simp only [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hv]
    refine (mul_le_mul_of_nonneg_left hI (inv_nonneg.2 hv.le)).trans (le_of_eq ?_)
    rw [mul_comm (C / X.nfac la x) _, ← mul_assoc, inv_mul_cancel₀ hv.ne', one_mul]
  · simp [hC]
  · simp [hC]
end ReciprocityTheory.ChartRestriction.G.FD.FlowCoefficientBounds
