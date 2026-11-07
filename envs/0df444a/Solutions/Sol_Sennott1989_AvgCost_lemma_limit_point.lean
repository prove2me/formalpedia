-- Prove2me | solution 1 for Sennott1989.AvgCost.lemma_limit_point
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T07:12:49.323554+00:00
-- url     : https://prove2.me/submissions/b8bf23d7-8fb0-430c-a597-d9ecbd2607b9

import Mathlib
import Definitions.Def_Sennott1989_AvgCost_Assumptions

open scoped ENNReal NNReal
open Filter Topology

open SennottDP.Discounted in
theorem solution {Act : Type} (M : MDC ℕ Act) (αs : ℕ → ℝ≥0)
    (hα0 : ∀ n, 0 < αs n) (hα1 : ∀ n, αs n < 1) (hlim : Tendsto αs atTop (𝓝 1))
    (fs : ℕ → StationaryPolicy M)
    (hfs : ∀ n, Realizes M (fs n) (αs n) (valueFn M (αs n))) :
    ∃ f : StationaryPolicy M, IsLimitPoint M fs f := by
  letI : ∀ i, TopologicalSpace {a : Act // a ∈ M.A i} := fun _ => ⊥
  haveI : ∀ i, DiscreteTopology {a : Act // a ∈ M.A i} := fun _ => ⟨rfl⟩
  haveI : ∀ i, Finite {a : Act // a ∈ M.A i} := fun i => (M.A i).finite_toSet.to_subtype
  haveI : ∀ i, CompactSpace {a : Act // a ∈ M.A i} := fun _ => Finite.compactSpace
  let x : ℕ → (∀ i, {a : Act // a ∈ M.A i}) := fun n i => ⟨(fs n).1 i, (fs n).2 i⟩
  obtain ⟨a, φ, hφ, ht⟩ := CompactSpace.tendsto_subseq x
  refine ⟨⟨fun i => (a i).1, fun i => (a i).2⟩, φ, hφ, fun i => ?_⟩
  have hti := (tendsto_pi_nhds.1 ht) i
  rw [nhds_discrete, tendsto_pure] at hti
  filter_upwards [hti] with k hk
  exact congrArg Subtype.val hk
