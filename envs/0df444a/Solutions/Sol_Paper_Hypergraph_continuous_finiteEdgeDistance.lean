-- Prove2me | solution 1 for Paper.Hypergraph.continuous_finiteEdgeDistance
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:10:50.186947+00:00
-- url     : https://prove2.me/submissions/4b2013a6-309a-4d98-b1b8-569ee9544232

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
theorem _root_.solution (H : Hypergraph) (e f : ℕ) :
    Continuous (H.finiteEdgeDistance e f) := by
  apply Continuous.finset_inf'_apply
  intro o ho
  cases o with
  | none => exact continuous_const
  | some S => exact continuous_finsetSum S (fun v _ => continuous_apply v)
end Paper.Hypergraph
