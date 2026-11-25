-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PolydiscLelongLimit_extend_by_zero_0f01477301e6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:47:43.320919+00:00
-- url     : https://prove2.me/submissions/07f258e2-c231-40c5-b273-42093f642d7a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPolydiscLelongLimit
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_ProjectiveLineZeroFormHolds
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_HessCRestrictThm
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_ContDiffOfContDiffOnZeroOff
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPolydiscLelongLimit
import Theorems.Thm_ReciprocityTheory_AnForm_A_contDiff_of_contDiffOn_zero_off


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open scoped ContDiff
noncomputable section
open GroundTheory.Heights₂.Heights.PolydiscLelongLimit
namespace GroundTheory.Heights₂.Heights.PolydiscLelongLimit
theorem _root_.solution {D : ℕ} {r ρ : ℝ} {χ : (Fin D → ℂ) → ℝ} (hρ : ρ < r)
    (hχ : ContDiffOn ℝ ∞ χ (Metric.ball 0 r))
    (hsupp : ∀ τ ∈ Metric.ball (0 : Fin D → ℂ) r, χ τ ≠ 0 → τ ∈ Metric.ball 0 ρ) :
    ContDiff ℝ ∞ ((Metric.ball (0 : Fin D → ℂ) r).indicator χ) ∧
      HasCompactSupport ((Metric.ball (0 : Fin D → ℂ) r).indicator χ) ∧
      tsupport ((Metric.ball (0 : Fin D → ℂ) r).indicator χ) ⊆ Metric.closedBall 0 ρ ∧
      Set.EqOn ((Metric.ball (0 : Fin D → ℂ) r).indicator χ) χ (Metric.ball 0 r) := by
  have h0 : ∀ τ ∉ Metric.closedBall (0 : Fin D → ℂ) ρ,
      (Metric.ball (0 : Fin D → ℂ) r).indicator χ τ = 0 := by
    intro τ hτ
    by_cases hU : τ ∈ Metric.ball (0 : Fin D → ℂ) r
    · rw [Set.indicator_of_mem hU]
      by_contra h
      exact hτ (Metric.ball_subset_closedBall (hsupp τ hU h))
    · exact Set.indicator_of_notMem hU _
  have heq : Set.EqOn ((Metric.ball (0 : Fin D → ℂ) r).indicator χ) χ (Metric.ball 0 r) :=
    fun τ hτ => Set.indicator_of_mem hτ _
  exact ⟨contDiff_of_contDiffOn_zero_off Metric.isOpen_ball Metric.isClosed_closedBall
    (Metric.closedBall_subset_ball hρ) (hχ.congr heq) h0,
    HasCompactSupport.intro (isCompact_closedBall 0 ρ) h0,
    closure_minimal (fun τ hτ => by_contra fun h => (Function.mem_support.1 hτ) (h0 τ h))
      Metric.isClosed_closedBall, heq⟩
end GroundTheory.Heights₂.Heights.PolydiscLelongLimit
