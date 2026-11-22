-- Prove2me | solution 1 for Paper.Hypergraph.compact_separatorCube
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:11:37.635731+00:00
-- url     : https://prove2.me/submissions/284645d3-e9fd-4e7f-80f6-c5cde0d9fe66

import Definitions.Def_Paper_TrustBoundary
import Definitions.Def_Paper_Formalized
import Theorems.Thm_Paper_Hypergraph_continuous_finiteEdgeDistance

set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper
open Paper.Hypergraph
namespace Paper.Hypergraph
theorem _root_.solution (H : Hypergraph) (γ : ℕ → ℝ) (θ : ℝ) :
    IsCompact (H.separatorCube γ θ) := by
  apply isCompact_Icc.inter_right
  simp only [Set.setOf_forall]
  apply isClosed_iInter
  intro e
  apply isClosed_iInter
  intro he
  apply isClosed_le continuous_const
  exact continuous_finsetSum _ (fun f _ => continuous_const.mul (H.continuous_finiteEdgeDistance e f))
end Paper.Hypergraph
