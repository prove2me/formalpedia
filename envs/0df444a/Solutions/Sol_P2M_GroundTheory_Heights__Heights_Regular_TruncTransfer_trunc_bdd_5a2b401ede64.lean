-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Regular_TruncTransfer_trunc_bdd_5a2b401ede64
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:02:32.241701+00:00
-- url     : https://prove2.me/submissions/74b2ee87-dfc6-4b84-8900-f9789b4f0785

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_StatementsTruncTransfer
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_GlueCharts
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PTruncTransfer
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_TruncTransfer_limsupExt_max_le_2c44b518e346
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_TruncTransfer_isCompact_chart_image_aa5560298c9d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_RegChartData_symm_mem_Yo_ad344fcd4555


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Regular
open Metric Filter Topology Set
open ReciprocityTheory.AnForm.A (coordDiv limsupExt polyMax)
open ReciprocityTheory.AnForm.M (FinHolAtlas IsCompatChart)
noncomputable section
open GroundTheory.Heights₂.Heights.Regular.TruncTransfer
variable {D : ℕ} {X : Type*} [TopologicalSpace X] [CompactSpace X] {A : FinHolAtlas D X}
  (R : RegChartData A)
namespace GroundTheory.Heights₂.Heights.Regular.TruncTransfer
theorem _root_.solution (k : Fin R.N) : ∃ c > 0, ∃ M : ℝ, ∀ K : ℝ, ∀ x ∈ R.mid k, ∀ s ≤ c,
    ∀ y ∈ closedBall (R.chart k x) s, R.trunc K k y ≤ max M (-K) := by
  have hKk := isCompact_chart_image R k subset_rfl isClosed_closure
  obtain ⟨ε, hε, hεT⟩ := hKk.exists_cthickening_subset_open (R.chart k).open_target
    (image_subset_iff.2 fun x hx => (R.chart k).map_source (R.closure_mid k hx))
  have hc : IsCompact (cthickening ε (R.chart k '' closure (R.mid k))) := hKk.cthickening
  obtain ⟨Mq, hMq⟩ := hc.exists_bound_of_continuousOn ((R.q_smooth k).continuousOn.mono hεT)
  refine ⟨ε / 2, half_pos hε, Mq + R.Cph, fun K x hx s hs y hy => ?_⟩
  have hxK : R.chart k x ∈ R.chart k '' closure (R.mid k) := mem_image_of_mem _ (subset_closure hx)
  have hball := closedBall_subset_cthickening hxK ε
  have hyε : dist y (R.chart k x) ≤ ε / 2 := (mem_closedBall.1 hy).trans hs
  have hyT : y ∈ (R.chart k).target := hεT (hball (mem_closedBall.2 (by linarith)))
  refine limsupExt_max_le (R.chart k).open_target _ _ K _ _ hyT (half_pos hε)
    fun y' hy' hy'T hy'S => ?_
  have hy'c : y' ∈ cthickening ε (R.chart k '' closure (R.mid k)) :=
    hball (mem_closedBall.2 (by linarith [dist_triangle y' y (R.chart k x), mem_ball.1 hy']))
  have hq : R.q k y' ≤ Mq := (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hMq y' hy'c)
  have hph := R.ph_le _ (R.symm_mem_Yo k hy'T hy'S)
  refine max_le_max ?_ le_rfl
  show R.q k y' + R.ph ((R.chart k).symm y') ≤ Mq + R.Cph
  linarith
end GroundTheory.Heights₂.Heights.Regular.TruncTransfer
