-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__CD_eventually_pair_16eb6f15237a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:30:56.894326+00:00
-- url     : https://prove2.me/submissions/eeb332ff-0aa3-4ed4-a093-15bd1fb1ffd0

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_HasStrictFDerivAtExpZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.BasicNotions.Examples₂.CD
open Filter Topology Metric NormedSpace Asymptotics
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]
namespace Formalism.BasicNotions.Examples₂.CD
theorem _root_.solution {P : 𝔸 × 𝔸 → Prop} (h : ∀ᶠ p in 𝓝 (0 : 𝔸 × 𝔸), P p) :
    ∃ δ > 0, ∀ X Y : 𝔸, ‖X‖ < δ → ‖Y‖ < δ → P (X, Y) := by
  obtain ⟨δ, hδ, hP⟩ := Metric.eventually_nhds_iff.1 h
  refine ⟨δ, hδ, fun X Y hX hY => hP ?_⟩
  rw [dist_zero_right, Prod.norm_def]
  exact max_lt hX hY
end Formalism.BasicNotions.Examples₂.CD
