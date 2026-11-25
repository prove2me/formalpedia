-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf.poincareLift_locally_squareIntegrable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:46:47.063601+00:00
-- url     : https://prove2.me/submissions/1f83b0d5-0634-4f15-b8cd-005ccea449c9

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExtFStatementPfA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExtFStatementPfB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExtFPf_nfac_contOn
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExtFPf_Gf_meas
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExtFPf_Gf_inv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExtFPf_Gf_cpt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExtFPf_norm_poincareLift_sq_le
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExtFPf_ae_OmF
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



set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Metric
open scoped ENNReal Matrix
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
variable {X} {x0 : Frame X.Ψ r} (D : LUData X x0) (la : Wt X.Ψ r) (F : V (nd X) → ℂ)
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf
theorem _root_.solution (hM : FrameMeasStatement (E := E)) (hx0 : IsOrth X x0)
    (hF : DifferentiableOn ℂ F (OmF X x0))
    (hL2 : ∀ C : Set (Frame X.Ψ r), IsCompact C → C ⊆ X.dom →
      ∫⁻ z in sat X x0 C, ENNReal.ofReal (‖F z‖ ^ 2 * Real.exp (-phla X la (cpt X x0 z))) ∂muF X x0 < ⊤)
    {C : Set (Frame X.Ψ r)} (hC : IsCompact C) (hCd : C ⊆ X.dom) :
    ∫⁻ x in C, ENNReal.ofReal (‖P0 D la F x‖ ^ 2) < ⊤ := by
  obtain ⟨K, hK, hKG⟩ := hM r X x0 hx0 C hC hCd
  obtain ⟨m, hm, hmC⟩ : ∃ m : ℝ, 0 < m ∧ ∀ x ∈ C, m ≤ X.nfac la x := by
    rcases C.eq_empty_or_nonempty with h | h
    · exact ⟨1, one_pos, by simp [h]⟩
    obtain ⟨x1, hx1, hmin⟩ := hC.exists_isMinOn h ((nfac_contOn X la).mono hCd)
    exact ⟨X.nfac la x1, FlowCoefficientBounds.nfac_pos X (hCd hx1) la, fun x hx => hmin hx⟩
  have h1 : ∫⁻ x in C, ENNReal.ofReal (‖P0 D la F x‖ ^ 2) ≤
      ENNReal.ofReal ((m ^ 2)⁻¹) * ∫⁻ x in C, Gf D la F x := by
    rw [← lintegral_const_mul _ (Gf_meas D la F hF)]
    exact setLIntegral_mono' hC.measurableSet fun x hx => norm_poincareLift_sq_le D la F (hCd hx) hm (hmC x hx)
  have h2 := hKG (Gf D la F) (Gf_meas D la F hF) fun x hx b hb => Gf_inv D la F hx hb
  have h3 : ∫⁻ z in sat X x0 C, Gf D la F (cpt X x0 z) ∂muF X x0 ≤
      ∫⁻ z in sat X x0 C, ENNReal.ofReal (‖F z‖ ^ 2 * Real.exp (-phla X la (cpt X x0 z))) ∂muF X x0 := by
    refine lintegral_mono_ae ?_
    filter_upwards [ae_restrict_of_ae (ae_OmF (x0 := x0))] with z hz
    rw [Gf_cpt D la F hz]
  calc ∫⁻ x in C, ENNReal.ofReal (‖P0 D la F x‖ ^ 2)
      ≤ ENNReal.ofReal ((m ^ 2)⁻¹) * (K * ∫⁻ z in sat X x0 C,
          ENNReal.ofReal (‖F z‖ ^ 2 * Real.exp (-phla X la (cpt X x0 z))) ∂muF X x0) :=
        h1.trans (mul_le_mul' le_rfl (h2.trans (mul_le_mul' le_rfl h3)))
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.mul_lt_top hK (hL2 C hC hCd))
end ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf
