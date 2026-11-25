-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.CuspCoefficientFlow.fj_hbd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:59:35.084884+00:00
-- url     : https://prove2.me/submissions/4262787f-0179-49cb-b651-fe875e9b99a9

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCoefficientDomain
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowCoefficientBounds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspCoefficientFlow
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_CuspCoefficientFlow_flowL_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_CuspCoefficientFlow_cont_dmin
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_CuspCoefficientFlow_continuousAt_nfac
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FlowCoefficientBounds_flow_real
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FlowCoefficientBounds_nfac_pos
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


section
namespace ReciprocityTheory.ChartRestriction.G.FD.CuspCoefficientFlow
open NumberField Complex ReciprocityTheory.ChartRestriction.G.FD MeasureTheory Metric Set Filter
open scoped ComplexConjugate Topology
noncomputable section
section Param
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
  [MeasurableSpace F] [BorelSpace F] {ι : Type} [Fintype ι]
end Param
section Frame
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
private theorem isOpen_dom_upper_bounds : IsOpen X.dom := by
  have hset : X.dom = ⋂ τ : X.Ψ, ({x : Frame X.Ψ r | (mat x τ).det ≠ 0} ∩
      ⋂ i : Fin (r + 1), {x | 0 < psgn X.p0 i * (dmin X.Gm x τ i).re}) := by
    ext x
    simp [Data.dom, GG]
  rw [hset]
  refine isOpen_iInter_of_finite fun τ => IsOpen.inter ?_ (isOpen_iInter_of_finite fun i => ?_)
  · exact isOpen_ne_fun
      ((show Continuous fun x : Frame X.Ψ r => mat x τ from continuous_apply τ).matrix_det)
      continuous_const
  · exact isOpen_lt continuous_const
      (continuous_const.mul (Complex.continuous_re.comp (cont_dmin X τ i)))
end Frame
end
end ReciprocityTheory.ChartRestriction.G.FD.CuspCoefficientFlow
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.CuspCoefficientFlow
open NumberField Complex ReciprocityTheory.ChartRestriction.G.FD MeasureTheory Metric Set Filter
open scoped ComplexConjugate Topology
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.FD.CuspCoefficientFlow
theorem _root_.solution (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (hP : X.IsBddSec la P) {ξ : Fin r → E}
    (hξ : X.IsIso ξ) : ∀ x0 ∈ X.dom, ∃ ρ > 0, ∃ C, closedBall x0 ρ ⊆ X.dom ∧
      ∀ t : X.Ψ → ℝ, ∀ z ∈ closedBall x0 ρ, ‖P (flowL X ξ t z)‖ ≤ C := by
  intro x0 hx0
  obtain ⟨-, C, hC⟩ := hP
  have hpos := FlowCoefficientBounds.nfac_pos X hx0 la
  have hcont := continuousAt_nfac X la hx0
  have hev : ∀ᶠ z in 𝓝 x0, X.nfac la x0 / 2 < X.nfac la z ∧ z ∈ X.dom :=
    (hcont.eventually (lt_mem_nhds (by linarith : X.nfac la x0 / 2 < X.nfac la x0))).and
      ((isOpen_dom_upper_bounds X).mem_nhds hx0)
  obtain ⟨ρ, hρ, hball⟩ := Metric.mem_nhds_iff.mp hev
  refine ⟨ρ / 2, by positivity, 2 * C / X.nfac la x0, ?_, ?_⟩
  · intro z hz
    exact (hball (Metric.closedBall_subset_ball (by linarith) hz)).2
  · intro t z hz
    have hz' := hball (Metric.closedBall_subset_ball (by linarith) hz)
    obtain ⟨hfd, hfn⟩ := FlowCoefficientBounds.flow_real X hξ hz'.2 t la
    have h1 := hC _ hfd
    rw [flowL_apply]
    have h2 : X.pnorm la P (X.flow ξ (fun τ => (t τ : ℂ)) z) =
        ‖P (X.flow ξ (fun τ => (t τ : ℂ)) z)‖ * X.nfac la z := by
      rw [← hfn]
      rfl
    rw [h2] at h1
    have h3 : ‖P (X.flow ξ (fun τ => (t τ : ℂ)) z)‖ * (X.nfac la x0 / 2) ≤
        ‖P (X.flow ξ (fun τ => (t τ : ℂ)) z)‖ * X.nfac la z :=
      mul_le_mul_of_nonneg_left hz'.1.le (norm_nonneg _)
    rw [le_div_iff₀ hpos]
    linarith
end ReciprocityTheory.ChartRestriction.G.FD.CuspCoefficientFlow
