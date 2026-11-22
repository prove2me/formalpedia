-- Prove2me | solution 1 for Paper.Hypergraph.vertexDistance_congr_on_vertices
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:15:56.613406+00:00
-- url     : https://prove2.me/submissions/419219a5-34f4-4c58-ba0f-7ea3c837ea5f

import Definitions.Def_Paper_RoundingPaths
import Definitions.Def_Paper_RoundingSeparation
import Theorems.Thm_Paper_Hypergraph_vertexDistance_mono


set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper Paper.Hypergraph
namespace Paper.Hypergraph
theorem _root_.solution (H : Hypergraph) {x y : ℕ → ℝ}
    (hx : ∀ v ∈ H.vertices, 0 ≤ x v) (hxy : ∀ v ∈ H.vertices, x v = y v)
    {u v : ℕ} (hu : u ∈ H.vertices) : H.vertexDistance x u v = H.vertexDistance y u v := by
  apply le_antisymm (H.vertexDistance_mono hx (fun z hz => (hxy z hz).le) hu)
  apply H.vertexDistance_mono (fun z hz => by rw [← hxy z hz]; exact hx z hz)
    (fun z hz => (hxy z hz).symm.le) hu
end Paper.Hypergraph
