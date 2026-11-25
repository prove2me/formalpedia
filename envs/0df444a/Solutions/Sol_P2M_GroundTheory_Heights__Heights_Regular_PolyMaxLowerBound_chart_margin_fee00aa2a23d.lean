-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Regular_PolyMaxLowerBound_chart_margin_fee00aa2a23d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:49:02.572642+00:00
-- url     : https://prove2.me/submissions/4d053877-d0f3-4512-a3e1-73d20481918a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PPolyMaxLowerBound

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
open Metric Set
open ReciprocityTheory.AnForm.A (polyMax coordDiv limsupExt)
open ReciprocityTheory.AnForm.M (FinHolAtlas)
noncomputable section
namespace GroundTheory.Heights₂.Heights.Regular
namespace PolyMaxLowerBound
theorem _root_.solution {X : Type} [TopologicalSpace X] [CompactSpace X] {D : ℕ}
    {A : FinHolAtlas D X} (R : RegChartData A) (j : Fin R.N) :
    ∃ δ Q : ℝ, 0 < δ ∧ 0 ≤ Q ∧ ∀ x ∈ R.mid j, ∀ y ∈ closedBall (R.chart j x) δ,
      y ∈ (R.chart j).target ∧ |R.q j y| ≤ Q := by
  have hK : IsCompact ((R.chart j) '' closure (R.mid j)) :=
    isClosed_closure.isCompact.image_of_continuousOn
      ((R.chart j).continuousOn.mono (R.closure_mid j))
  have hKT : (R.chart j) '' closure (R.mid j) ⊆ (R.chart j).target := by
    rintro _ ⟨x, hx, rfl⟩
    exact (R.chart j).map_source (R.closure_mid j hx)
  obtain ⟨δ, hδ, hsub⟩ := hK.exists_cthickening_subset_open (R.chart j).open_target hKT
  obtain ⟨Q, hQ⟩ := (hK.cthickening (r := δ)).exists_bound_of_continuousOn
    ((R.q_smooth j).continuousOn.mono hsub)
  refine ⟨δ, max Q 0, hδ, le_max_right _ _, fun x hx y hy => ?_⟩
  have hy' : y ∈ cthickening δ ((R.chart j) '' closure (R.mid j)) :=
    closedBall_subset_cthickening (mem_image_of_mem _ (subset_closure hx)) δ hy
  refine ⟨hsub hy', ?_⟩
  have := hQ y hy'
  rw [Real.norm_eq_abs] at this
  exact this.trans (le_max_left _ _)
end PolyMaxLowerBound
end GroundTheory.Heights₂.Heights.Regular
