-- Prove2me | solution 1 for Paper.Hypergraph.separatorRegion_no_crossing_edge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:21:42.625323+00:00
-- url     : https://prove2.me/submissions/2bd7db6e-aed7-4455-8335-2fd0727f23e2

import Definitions.Def_Paper_RoundingPaths
import Definitions.Def_Paper_RoundingSeparation
import Theorems.Thm_Paper_Hypergraph_separatorRegion_closed

set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper Paper.Hypergraph
namespace Paper.Hypergraph
theorem _root_.solution (H : Hypergraph) (A S : Finset ℕ)
    {e : ℕ} (he : e ∈ H.edges) :
    Disjoint (H.edge e) (H.separatorRegion A S) ∨
      Disjoint (H.edge e) (H.vertices \ (H.separatorRegion A S ∪ S)) := by
  by_contra hn
  obtain ⟨hu, hv⟩ := not_or.mp hn
  obtain ⟨u, hue, huP⟩ := not_disjoint_iff.mp hu
  obtain ⟨v, hve, hvP⟩ := not_disjoint_iff.mp hv
  have hv := mem_sdiff.mp hvP
  have hnP : v ∉ H.separatorRegion A S := fun h => hv.2 (mem_union_left _ h)
  have hnS : v ∉ S := fun h => hv.2 (mem_union_right _ h)
  have huv : u ≠ v := by intro h; subst v; exact hnP huP
  exact hnP (H.separatorRegion_closed A S huP (mem_sdiff.mpr ⟨hv.1, hnS⟩)
    ⟨huv, e, he, hue, hve⟩)
end Paper.Hypergraph
