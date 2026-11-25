-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.LUPf.dense_delta
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:03:18.970515+00:00
-- url     : https://prove2.me/submissions/27b0fd67-3303-46eb-b90b-3a4bdfcd989f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_LUStatementPfC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_LUStatementPf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_LUPf_orthogonalFrame_delta_eq_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_LUPf_linePoly_eval
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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.LUPf
open Matrix NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf
  Metric Polynomial
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r} {x0 : Frame X.Ψ r}
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.LUPf
theorem _root_.solution (hx0 : IsOrth X x0) (x : Frame X.Ψ r) (ε : ℝ) (hε : 0 < ε) :
    ∃ y ∈ ball x ε, DeltaF X x0 y ≠ 0 := by
  classical
  set w : Frame X.Ψ r := x0 - x
  set P := linePoly (x0 := x0) x w
  have hP1 : P.eval 1 = 1 := by
    rw [linePoly_eval, one_smul, add_sub_cancel, orthogonalFrame_delta_eq_one hx0]
  have hP0 : P ≠ 0 := by
    rintro h
    rw [h, Polynomial.eval_zero] at hP1
    exact zero_ne_one hP1
  set δ : ℝ := ε / (‖w‖ + 1)
  have hδ : 0 < δ := div_pos hε (by positivity)
  have hinf : ((fun s : ℝ => (s : ℂ)) '' Set.Ioo 0 δ).Infinite :=
    (Set.Ioo_infinite hδ).image (fun a _ b _ h => Complex.ofReal_injective h)
  obtain ⟨c, hc, hcP⟩ := (hinf.diff (Polynomial.finite_setOf_isRoot hP0)).nonempty
  obtain ⟨s, hs, rfl⟩ := hc
  refine ⟨x + (s : ℂ) • w, ?_, ?_⟩
  · rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hs.1]
    calc s * ‖w‖ ≤ δ * ‖w‖ := by gcongr; exact hs.2.le
      _ < δ * (‖w‖ + 1) := by gcongr; linarith
      _ = ε := by
        have : (‖w‖ + 1) ≠ 0 := by positivity
        simp only [δ]
        field_simp
  · rw [← linePoly_eval]
    exact hcP
end ReciprocityTheory.ChartRestriction.G.AR.Up.LUPf
