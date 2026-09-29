-- Prove2me | solution 1 for SocialEquilibrium.Existence.isClosed_graph_prod
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T22:32:21.504078+00:00
-- url     : https://prove2.me/submissions/3747153e-3b07-4ef5-a762-e657415b0ab2

import Mathlib
import Definitions.Def_SocialEquilibrium_Existence_graph
import Definitions.Def_SocialEquilibrium_Existence_Game

namespace SocialEquilibrium.Existence

theorem aux_icgp_others_continuous {ι : Type*} [DecidableEq ι]
    {E : ι → Type*} [∀ i, TopologicalSpace (E i)]
    (X : ∀ i, Set (E i)) (i : ι) :
    Continuous (others X i) := by
  unfold others
  exact continuous_pi fun j => continuous_apply (j : ι)

end SocialEquilibrium.Existence

open SocialEquilibrium.Existence

theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι]
    {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
    [∀ i, FiniteDimensional ℝ (E i)]
    (X : ∀ i, Set (E i)) (M : ∀ i : ι, Set (Others X i × X i))
    (hM : ∀ i, IsClosed (M i)) :
    IsClosed (graph fun a : ∀ j, X j =>
      {a' : ∀ j, X j | ∀ i, (others X i a, a' i) ∈ M i}) := by
  have h : (graph fun a : ∀ j, X j =>
      {a' : ∀ j, X j | ∀ i, (others X i a, a' i) ∈ M i}) =
      ⋂ i, (fun p : (∀ j, X j) × (∀ j, X j) => (others X i p.1, p.2 i)) ⁻¹' M i := by
    ext p
    simp [graph]
  rw [h]
  refine isClosed_iInter fun i => (hM i).preimage ?_
  exact ((aux_icgp_others_continuous X i).comp continuous_fst).prodMk
    ((continuous_apply i).comp continuous_snd)
