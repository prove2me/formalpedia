-- Prove2me | solution 1 for Paper.Hypergraph.child_card_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:11:42.848116+00:00
-- url     : https://prove2.me/submissions/c4c941f1-808f-4c0d-8b25-54da9da47ac5

import Definitions.Def_Paper_TrustBoundary
import Definitions.Def_Paper_Formalized

set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper
open Paper.Hypergraph
namespace Paper.Hypergraph
theorem _root_.solution (H : Hypergraph) {W Z B K : Finset ℕ} {u : ℕ}
    (hZB : Z ⊆ B) (hu : u ∈ W \ Z) (huB : u ∈ B)
    (hK : K ∈ (H.induce (W \ B)).components) : K.card < (W \ Z).card := by
  have hsub : K ⊆ W \ B := fun v hv =>
    (mem_inter.mp (mem_powerset.mp (mem_filter.mp hK).1 hv)).2
  apply card_lt_card
  refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
  · intro v hv
    exact mem_sdiff.mpr ⟨(mem_sdiff.mp (hsub hv)).1,
      fun hz => (mem_sdiff.mp (hsub hv)).2 (hZB hz)⟩
  · intro heq
    have huK : u ∈ K := heq ▸ hu
    exact (mem_sdiff.mp (hsub huK)).2 huB
end Paper.Hypergraph
