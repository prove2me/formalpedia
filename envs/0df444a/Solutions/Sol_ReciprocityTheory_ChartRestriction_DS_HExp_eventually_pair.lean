-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.HExp.eventually_pair
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:11:39.208921+00:00
-- url     : https://prove2.me/submissions/f9a65899-43c4-4b47-b712-484a40222dfe

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_FormalDegree_HaarVolumes_HaarExpA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_FormalDegree_HaarVolumes_HaarExpB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.HExp
open Filter Topology Metric NormedSpace Asymptotics
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]
namespace ReciprocityTheory.ChartRestriction.DS.HExp
theorem _root_.solution {P : 𝔸 × 𝔸 → Prop} (h : ∀ᶠ p in 𝓝 (0 : 𝔸 × 𝔸), P p) :
    ∃ δ > 0, ∀ X Y : 𝔸, ‖X‖ < δ → ‖Y‖ < δ → P (X, Y) := by
  obtain ⟨δ, hδ, h⟩ := Metric.eventually_nhds_iff_ball.mp h
  refine ⟨δ, hδ, fun X Y hX hY => h _ ?_⟩
  rw [mem_ball_zero_iff, Prod.norm_def]
  exact max_lt hX hY
end ReciprocityTheory.ChartRestriction.DS.HExp
