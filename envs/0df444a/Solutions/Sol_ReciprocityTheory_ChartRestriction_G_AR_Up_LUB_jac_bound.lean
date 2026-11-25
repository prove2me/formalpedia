-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.LUB.jac_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:36:42.526104+00:00
-- url     : https://prove2.me/submissions/3e6ebfcd-2936-4eae-ad2f-92d5b33e214d

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_LocalUnfoldPfA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_OntoStatementPfB
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_HoloSmooth
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_LocalUnfoldPfB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_LUB_isOpen_Uc
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_LUB___cdOn_a8a5534150e7
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_IW_V_zero_app
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
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_mono
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.G.AR.Up.IW.V_zero_app
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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.LUB
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ENNReal ContDiff
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
  {x1' : Frame X.Ψ r} (b1 : Frame X.Ψ r) (D : ExtFPf.LUData X x1')
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.LUB
theorem _root_.solution {ρ0 : ℝ} (hsub : Metric.closedBall (0 : V (nd X)) ρ0 ⊆ Uc X b1 D) :
    ∃ Kj : ℝ, ∀ z ∈ Metric.closedBall (0 : V (nd X)) ρ0, |(fderiv ℝ (Φ X b1 D) z).det| ≤ Kj := by
  have hcd : ContDiffOn ℝ ∞ (Φ X b1 D) (Uc X b1 D) := (Φ_cdOn X b1 D).restrict_scalars ℝ
  have hfd : ContinuousOn (fun z => fderiv ℝ (Φ X b1 D) z) (Uc X b1 D) :=
    hcd.continuousOn_fderiv_of_isOpen (isOpen_Uc X b1 D) (by simp)
  have hdet : ContinuousOn (fun z => (fderiv ℝ (Φ X b1 D) z).det) (Uc X b1 D) :=
    ContinuousLinearMap.continuous_det.comp_continuousOn hfd
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : V (nd X)) ρ0).exists_bound_of_continuousOn (hdet.mono hsub)
  exact ⟨C, fun z hz => by simpa [Real.norm_eq_abs] using hC z hz⟩
end ReciprocityTheory.ChartRestriction.G.AR.Up.LUB
