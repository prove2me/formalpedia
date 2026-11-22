-- Prove2me | solution 1 for Paper.Hypergraph.separatorRegion_disjoint_terminals
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:15:30.585681+00:00
-- url     : https://prove2.me/submissions/7f0f566a-6100-49bb-9b77-8fa0c1762b4a

import Definitions.Def_Paper_RoundingPaths
import Definitions.Def_Paper_RoundingSeparation

set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper Paper.Hypergraph
namespace Paper.Hypergraph
theorem _root_.solution (H : Hypergraph) {A B S : Finset ℕ}
    (hsep : H.IntegralSeparator A B S) : Disjoint (H.separatorRegion A S) B := by
  apply disjoint_left.mpr
  intro b hb hbB
  obtain ⟨hbV, a, ha, hab⟩ := mem_filter.mp hb
  exact hsep.2 a ha b (mem_sdiff.mpr ⟨hbB, (mem_sdiff.mp hbV).2⟩) hab
end Paper.Hypergraph
