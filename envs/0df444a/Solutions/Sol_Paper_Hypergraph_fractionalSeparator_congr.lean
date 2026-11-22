-- Prove2me | solution 1 for Paper.Hypergraph.fractionalSeparator_congr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:16:47.857822+00:00
-- url     : https://prove2.me/submissions/f5ec771f-4ce0-4b78-b769-9d5096fb9933

import Definitions.Def_Paper_RoundingPaths
import Definitions.Def_Paper_RoundingSeparation
import Theorems.Thm_Paper_Hypergraph_vertexDistance_congr_on_vertices

set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper Paper.Hypergraph
namespace Paper.Hypergraph
theorem _root_.solution (H : Hypergraph) {A B : Finset ℕ} {x y : ℕ → ℝ}
    (hA : A ⊆ H.vertices) (hx : H.FractionalSeparator A B x)
    (hxy : ∀ v ∈ H.vertices, x v = y v) : H.FractionalSeparator A B y := by
  constructor
  · intro v hv
    rw [← hxy v hv]
    exact hx.1 v hv
  · intro u hu v hv
    rw [← H.vertexDistance_congr_on_vertices (fun z hz => (hx.1 z hz).1) hxy (hA hu)]
    exact hx.2 u hu v hv
end Paper.Hypergraph
