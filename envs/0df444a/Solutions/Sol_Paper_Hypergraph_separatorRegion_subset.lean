-- Prove2me | solution 1 for Paper.Hypergraph.separatorRegion_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:15:11.582129+00:00
-- url     : https://prove2.me/submissions/6be52dee-822a-436f-a4a7-b32c79f6367f

import Definitions.Def_Paper_RoundingPaths
import Definitions.Def_Paper_RoundingSeparation

set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper Paper.Hypergraph
namespace Paper.Hypergraph
theorem _root_.solution (H : Hypergraph) (A S : Finset ℕ) :
    H.separatorRegion A S ⊆ H.vertices \ S := filter_subset _ _
end Paper.Hypergraph
