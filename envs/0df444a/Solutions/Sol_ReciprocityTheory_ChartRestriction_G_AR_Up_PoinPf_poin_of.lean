-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf.poin_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:58:58.733401+00:00
-- url     : https://prove2.me/submissions/910eb315-0746-488f-be5b-aae977cac059

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_PoinStatementPfA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_PoinStatementPfB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_PoinPf_differentiable_lact
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_PoinPf_enorm_poin_le
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_PoinPf_supR_le
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_PoinPf_pnorm_orth__e2bbf64ac7ff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_PoinPf_differentiableOn_tsum_loc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_PoinPf_isOpenDom
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_PoinPf_lactDom
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_PoinPf_norm_chi
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_PoinPf_poin_lact
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_PoinPf_poin_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_PoinPf_poin_rmul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_PoinPf_rmulDom
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FrameDegreeData_bOf_mem
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FrameDegreeData_ortho_bOf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FrameDegreeData_pnorm_rmul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ENNReal Matrix
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf
theorem _root_.solution (hL : LocStatement (E := E)) (hB : BallStatement (E := E)) (hF : FFStatement (E := E)) :
    PoinStatement (E := E) := by
  intro r X x0 hx0 hPD la W bb hW hWl hbb F P hFd hA hP hPF
  have H : Hyp X x0 la W bb F P := ⟨hx0, hPD, hW, hWl, hbb, hFd, hA, hP, hPF⟩
  obtain ⟨c, hc, hcW⟩ := hWl
  have hterm : ∀ (γ : X.Γ) y, ‖(X.χ la γ.1)⁻¹ * P (lact γ.1 y)‖ = ‖P (lact γ.1 y)‖ := by
    intro γ y; rw [norm_mul, norm_inv, norm_chi X la γ.2, inv_one, one_mul]
  obtain ⟨C1, hC1⟩ := hB r X x0 la W bb F P H 1 one_pos le_rfl
  have horth : ∀ y ∈ X.dom, IsOrth X y → ‖poin X la P y‖ ≤ max C1 0 * (1 / c) ^ (1 / 2 : ℝ) := by
    intro y hy hyo
    have h1 := (enorm_poin_le X la P y).trans ((hC1 y hy hyo).trans
      (mul_le_mul_of_nonneg_left (supR_le X la W hc hcW 1 y) (zero_le)))
    have h2 : ENNReal.ofReal C1 * ENNReal.ofReal (1 / c) ^ (1 / 2 : ℝ) ≤
        ENNReal.ofReal (max C1 0 * (1 / c) ^ (1 / 2 : ℝ)) := by
      rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num),
        ENNReal.ofReal_mul (le_max_right _ _)]
      gcongr
      exact le_max_left _ _
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 (h1.trans h2)
  refine ⟨?_, ⟨⟨?_, ?_, ?_⟩, ?_⟩, hF r X x0 la W bb F P H, ?_, ?_⟩
  · intro x hx
    obtain ⟨ε, hε, u, hu, hub⟩ := hL r X x0 la W bb F P H x hx
    exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun γ => (hterm γ x).le.trans (hub γ x (Metric.mem_ball_self hε))) hu
  · unfold poin
    refine differentiableOn_tsum_loc (isOpenDom X) _ (fun γ => ?_) (fun x hx => ?_)
    · exact (differentiableOn_const _).mul
        (hP.1.comp (differentiable_lact γ.1).differentiableOn fun y hy => lactDom X γ.2 hy)
    · obtain ⟨ε, hε, u, hu, hub⟩ := hL r X x0 la W bb F P H x hx
      exact ⟨ε, hε, u, hu, fun γ y hy => (hterm γ y).le.trans (hub γ y hy)⟩
  · intro x hx b hb
    exact poin_rmul X la P hP.2 hx hb
  · intro γ hγ x _
    exact poin_lact X la P hγ x
  · refine ⟨max C1 0 * (1 / c) ^ (1 / 2 : ℝ), fun x hx => ?_⟩
    have hb := FrameDegreeData.bOf_mem X hx
    have ho : IsOrth X (rmul x (FrameDegreeData.bOf X x)) := FrameDegreeData.ortho_bOf X hx
    have hxb : rmul x (FrameDegreeData.bOf X x) ∈ X.dom := rmulDom X hb hx
    rw [← FrameDegreeData.pnorm_rmul X la _ (fun y hy b hb => poin_rmul X la P hP.2 hy hb) x hx _ hb,
      pnorm_orth' X la _ ho]
    exact horth _ hxb ho
  · intro ρ hρ hρ1
    obtain ⟨C, hC⟩ := hB r X x0 la W bb F P H ρ hρ hρ1
    exact ⟨C, fun x hx hxo => (enorm_poin_le X la P x).trans (hC x hx hxo)⟩
  · intro la' g hg x hx
    exact poin_mul X la la' P g hg x hx
end ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf
