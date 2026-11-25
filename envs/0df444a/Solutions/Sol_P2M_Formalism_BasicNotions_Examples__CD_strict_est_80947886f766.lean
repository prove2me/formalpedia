-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__CD_strict_est_80947886f766
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:30:48.822249+00:00
-- url     : https://prove2.me/submissions/6de3e928-f0ab-4d22-a710-145f2e95bff7

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
theorem _root_.solution {F : 𝔸 × 𝔸 → 𝔸} {F' : 𝔸 × 𝔸 →L[ℝ] 𝔸} (hF : HasStrictFDerivAt F F' 0)
    {ε : ℝ} (hε : 0 < ε) : ∃ δ > 0, ∀ X Y : 𝔸, ‖X‖ < δ → ‖Y‖ < δ →
      ‖F (X, Y) - F (X, 0) - F' (0, Y)‖ ≤ ε * ‖Y‖ := by
  have h := hF.isLittleO.def hε
  obtain ⟨δ, hδ, hq⟩ := Metric.eventually_nhds_iff.1 h
  refine ⟨δ, hδ, fun X Y hX hY => ?_⟩
  have hd : dist ((X, Y), (X, (0 : 𝔸))) ((0 : 𝔸 × 𝔸), (0 : 𝔸 × 𝔸)) < δ := by
    rw [dist_eq_norm]
    have e : ((X, Y), (X, (0 : 𝔸))) - ((0 : 𝔸 × 𝔸), (0 : 𝔸 × 𝔸)) = ((X, Y), (X, 0)) := by simp
    rw [e, Prod.norm_def, Prod.norm_def, Prod.norm_def]
    simp only [norm_zero]
    exact max_lt (max_lt hX hY) (max_lt hX hδ)
  have h1 := hq hd
  beta_reduce at h1
  have e2 : ((X, Y) - (X, 0) : 𝔸 × 𝔸) = (0, Y) := by simp
  rw [e2, Prod.norm_def, norm_zero, max_eq_right (norm_nonneg _)] at h1
  exact h1
end Formalism.BasicNotions.Examples₂.CD
