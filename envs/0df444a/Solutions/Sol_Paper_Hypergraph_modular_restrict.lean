-- Prove2me | solution 1 for Paper.Hypergraph.modular_restrict
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:11:53.351248+00:00
-- url     : https://prove2.me/submissions/563fe613-b125-4630-8d9a-afca7783b2b1

import Definitions.Def_Paper_TrustBoundary
import Definitions.Def_Paper_Formalized
import Theorems.Thm_Paper_Hypergraph_modularWeight_vertex_le_one

set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper
open Paper.Hypergraph
namespace Paper.Hypergraph
theorem _root_.solution (H : Hypergraph) {w : ℕ → ℝ} (hw : H.ModularWeight w) :
    (fun v => if v ∈ H.vertices then w v else 0) ∈ H.modularCube := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro v; dsimp; split_ifs; exact hw.1 v; exact le_rfl
  · intro v; dsimp; split_ifs with hv
    · exact H.modularWeight_vertex_le_one hw hv
    · norm_num
  · intro e he
    convert hw.2 e he using 1
    apply sum_congr rfl
    intro v hv
    exact if_pos (H.edge_subset e he hv)
end Paper.Hypergraph
