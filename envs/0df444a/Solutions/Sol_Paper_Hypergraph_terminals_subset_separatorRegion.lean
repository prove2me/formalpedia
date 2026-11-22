-- Prove2me | solution 1 for Paper.Hypergraph.terminals_subset_separatorRegion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:15:30.153802+00:00
-- url     : https://prove2.me/submissions/3b81330c-bfb1-48ee-a855-99bf1e3c3b5f

import Definitions.Def_Paper_RoundingPaths
import Definitions.Def_Paper_RoundingSeparation

set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper Paper.Hypergraph
namespace Paper.Hypergraph
theorem _root_.solution (H : Hypergraph) {A S : Finset ℕ}
    (hA : A ⊆ H.vertices) : A \ S ⊆ H.separatorRegion A S := by
  intro a ha
  exact mem_filter.mpr ⟨mem_sdiff.mpr ⟨hA (mem_sdiff.mp ha).1, (mem_sdiff.mp ha).2⟩,
    a, ha, .rfl⟩
end Paper.Hypergraph
