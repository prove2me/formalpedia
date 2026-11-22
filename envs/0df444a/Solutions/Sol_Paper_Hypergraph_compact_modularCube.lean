-- Prove2me | solution 1 for Paper.Hypergraph.compact_modularCube
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:11:06.425055+00:00
-- url     : https://prove2.me/submissions/0820c61d-c3f0-4021-a50e-dece88f40328

import Definitions.Def_Paper_TrustBoundary
import Definitions.Def_Paper_Formalized

set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper
open Paper.Hypergraph
namespace Paper.Hypergraph
theorem _root_.solution (H : Hypergraph) : IsCompact H.modularCube := by
  apply isCompact_Icc.inter_right
  simp only [Set.setOf_forall]
  exact isClosed_iInter fun e => isClosed_iInter fun _ =>
    isClosed_le (continuous_finsetSum _ (fun v _ => continuous_apply v)) continuous_const
end Paper.Hypergraph
