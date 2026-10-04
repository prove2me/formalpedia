-- Prove2me | solution 1 for SennottDP.FiniteHorizon.stationary_limit_point
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T14:26:17.31626+00:00
-- url     : https://prove2.me/submissions/8b9ba06f-7269-42b4-a27f-96258721038c

import Mathlib
import Definitions.Def_SennottDP_FiniteHorizon_MDC
import Definitions.Def_SennottDP_FiniteHorizon_Criterion

open scoped ENNReal NNReal Topology
open Filter

open SennottDP.FiniteHorizon in
theorem solution {S Act : Type} [Countable S] (M : MDC S Act)
    (fs : ℕ → M.Stationary) : ∃ f : M.Stationary, M.IsLimitPoint fs f := by
  let _ : ∀ i, TopologicalSpace (M.A i) := fun _ => ⊥
  have : ∀ i, DiscreteTopology (M.A i) := fun _ => ⟨rfl⟩
  let x : ℕ → (∀ i, M.A i) := fun r i => ⟨(fs r).1 i, (fs r).2 i⟩
  obtain ⟨a, φ, hφ, hlim⟩ := CompactSpace.tendsto_subseq x
  refine ⟨⟨fun i => (a i).1, fun i => (a i).2⟩, φ, hφ, fun i => ?_⟩
  have h1 := (continuous_apply i).continuousAt.tendsto.comp hlim
  rw [nhds_discrete, tendsto_pure] at h1
  filter_upwards [h1] with k hk
  exact congrArg Subtype.val hk
