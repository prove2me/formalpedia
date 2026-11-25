-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.HExp.strict_est
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:09:57.775652+00:00
-- url     : https://prove2.me/submissions/2135cdd0-7ae5-44be-9271-62ad641d8c0c

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
theorem _root_.solution {F : 𝔸 × 𝔸 → 𝔸} {F' : 𝔸 × 𝔸 →L[ℝ] 𝔸} (hF : HasStrictFDerivAt F F' 0)
    {ε : ℝ} (hε : 0 < ε) : ∃ δ > 0, ∀ X Y : 𝔸, ‖X‖ < δ → ‖Y‖ < δ →
      ‖F (X, Y) - F (X, 0) - F' (0, Y)‖ ≤ ε * ‖Y‖ := by
  have h := hF.isLittleO.def hε
  obtain ⟨δ, hδ, h⟩ := Metric.eventually_nhds_iff_ball.mp h
  refine ⟨δ, hδ, fun X Y hX hY => ?_⟩
  have hm : (((X, Y), (X, 0)) : (𝔸 × 𝔸) × (𝔸 × 𝔸)) ∈ ball ((0 : 𝔸 × 𝔸), (0 : 𝔸 × 𝔸)) δ := by
    rw [show ((0 : 𝔸 × 𝔸), (0 : 𝔸 × 𝔸)) = 0 from rfl, mem_ball_zero_iff]
    simp only [Prod.norm_def, norm_zero]
    simp [hX, hY]
  have := h _ hm
  simpa [Prod.norm_def] using this
end ReciprocityTheory.ChartRestriction.DS.HExp
