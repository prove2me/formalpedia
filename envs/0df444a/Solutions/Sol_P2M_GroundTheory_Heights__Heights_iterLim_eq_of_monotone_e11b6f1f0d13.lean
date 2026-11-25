-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_iterLim_eq_of_monotone_e11b6f1f0d13
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:33:08.43628+00:00
-- url     : https://prove2.me/submissions/7bc11677-c637-4591-a0e8-0d5148ddca69

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_MonotoneDoubleLimit

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
open Filter Topology
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {T : ℝ → ℝ → ℝ} {A B : ℝ → ℝ} {a b : ℝ}
    (hε : ∀ δ, 0 < δ → ∀ ε, 0 < ε → ∀ ε', ε ≤ ε' → T ε δ ≤ T ε' δ)
    (hδ : ∀ ε, 0 < ε → ∀ δ, 0 < δ → ∀ δ', δ ≤ δ' → T ε δ ≤ T ε δ')
    (hA : ∀ δ, 0 < δ → Tendsto (fun ε => T ε δ) (𝓝[>] 0) (𝓝 (A δ)))
    (hB : ∀ ε, 0 < ε → Tendsto (fun δ => T ε δ) (𝓝[>] 0) (𝓝 (B ε)))
    (ha : Tendsto A (𝓝[>] 0) (𝓝 a)) (hb : Tendsto B (𝓝[>] 0) (𝓝 b)) : a = b := by
  have below : ∀ x : ℝ, 0 < x → ∀ᶠ y in 𝓝[>] (0 : ℝ), 0 < y ∧ y ≤ x := fun x hx => by
    filter_upwards [self_mem_nhdsWithin, (eventually_lt_nhds hx).filter_mono nhdsWithin_le_nhds]
      with y hy hyx using ⟨hy, hyx.le⟩
  have keyA : ∀ ε, 0 < ε → ∀ δ, 0 < δ → A δ ≤ T ε δ := fun ε hε0 δ hδ0 =>
    le_of_tendsto (hA δ hδ0) (by
      filter_upwards [below ε hε0] with ε' h' using hε δ hδ0 ε' h'.1 ε h'.2)
  have keyB : ∀ ε, 0 < ε → ∀ δ, 0 < δ → B ε ≤ T ε δ := fun ε hε0 δ hδ0 =>
    le_of_tendsto (hB ε hε0) (by
      filter_upwards [below δ hδ0] with δ' h' using hδ ε hε0 δ' h'.1 δ h'.2)
  have h1 : ∀ ε, 0 < ε → a ≤ B ε := fun ε hε0 =>
    le_of_tendsto_of_tendsto ha (hB ε hε0) (by
      filter_upwards [self_mem_nhdsWithin] with δ hδ using keyA ε hε0 δ hδ)
  have h2 : ∀ δ, 0 < δ → b ≤ A δ := fun δ hδ0 =>
    le_of_tendsto_of_tendsto hb (hA δ hδ0) (by
      filter_upwards [self_mem_nhdsWithin] with ε hε using keyB ε hε δ hδ0)
  refine le_antisymm ?_ ?_
  · exact ge_of_tendsto hb (by filter_upwards [self_mem_nhdsWithin] with ε hε using h1 ε hε)
  · exact ge_of_tendsto ha (by filter_upwards [self_mem_nhdsWithin] with δ hδ using h2 δ hδ)
end GroundTheory.Heights₂.Heights
