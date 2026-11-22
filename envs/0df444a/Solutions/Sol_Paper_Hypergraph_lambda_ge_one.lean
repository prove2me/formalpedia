-- Prove2me | solution 1 for Paper.Hypergraph.lambda_ge_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:12:53.229709+00:00
-- url     : https://prove2.me/submissions/a9ef43fa-fdd9-4cdc-9f2c-aa588bf9ee1f

import Definitions.Def_Paper_TrustBoundary
import Definitions.Def_Paper_Formalized
import Theorems.Thm_Paper_Hypergraph_degeneracy_ge_one

set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper
open Paper.Hypergraph
namespace Paper.Hypergraph
theorem _root_.solution (H : Hypergraph) (hne : H.vertices.Nonempty) :
    1 ≤ H.lambda := by
  exact le_min (by exact_mod_cast H.degeneracy_ge_one hne) (le_max_left _ _)
end Paper.Hypergraph
