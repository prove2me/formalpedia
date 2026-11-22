-- Prove2me | solution 1 for Paper.Hypergraph.independenceNumber_induce_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:16:45.632795+00:00
-- url     : https://prove2.me/submissions/3d1dc2f0-2e1c-4c70-b892-a11b4e6ede6d

import Definitions.Def_Paper_RoundingSeparation
import Definitions.Def_Paper_TwoTerminalRounding
import Theorems.Thm_Paper_Hypergraph_induce_induce
import Theorems.Thm_Paper_Hypergraph_structure_hereditary


set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper Paper.Hypergraph
namespace Paper.Hypergraph
theorem _root_.solution (H : Hypergraph) {U W : Finset ℕ} (hUW : U ⊆ W) :
    (H.induce U).independenceNumber ≤ (H.induce W).independenceNumber := by
  have h := ((H.induce W).structure_hereditary U).2
  rwa [H.induce_induce, inter_eq_right.mpr hUW] at h
end Paper.Hypergraph
