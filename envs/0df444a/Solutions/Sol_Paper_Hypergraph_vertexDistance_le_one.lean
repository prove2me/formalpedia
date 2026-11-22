-- Prove2me | solution 1 for Paper.Hypergraph.vertexDistance_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:52:25.176006+00:00
-- url     : https://prove2.me/submissions/b84acd4c-fe25-4cc2-8470-6d0653678dc0

import Definitions.Def_Paper_Formalized
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Definitions.Def_Paper_RoundingEstimates
import Theorems.Thm_Paper_Hypergraph_vertexDistance_le_option


set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper Paper.Hypergraph
namespace Paper.Hypergraph
theorem _root_.solution (H : Hypergraph) {x : ℕ → ℝ}
    (hx : ∀ v ∈ H.vertices, 0 ≤ x v) {u v : ℕ} (hu : u ∈ H.vertices) :
    H.vertexDistance x u v ≤ 1 :=
  H.vertexDistance_le_option hx hu (Set.mem_insert _ _)
end Paper.Hypergraph
