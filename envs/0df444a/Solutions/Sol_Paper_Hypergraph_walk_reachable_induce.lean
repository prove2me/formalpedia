-- Prove2me | solution 1 for Paper.Hypergraph.walk_reachable_induce
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:56:51.739807+00:00
-- url     : https://prove2.me/submissions/8323d5db-7337-47ff-8d6d-d9057e183bcc

import Definitions.Def_Paper_TrustBoundary
import Definitions.Def_Paper_Formalized
import Theorems.Thm_Paper_Hypergraph_primal_induce_adj

set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper
open Paper.Hypergraph
namespace Paper.Hypergraph
theorem _root_.solution (H : Hypergraph) {u v : ℕ} (p : H.primal.Walk u v)
    {W : Finset ℕ} (hW : ∀ z ∈ p.support, z ∈ W) :
    (H.induce W).primal.Reachable u v := by
  induction p with
  | nil => exact .rfl
  | @cons u v t huv p ih =>
    have huW := hW u (List.mem_cons_self)
    have hvW := hW v (List.mem_cons_of_mem _ p.start_mem_support)
    exact ((H.primal_induce_adj W huW hvW).mpr huv).reachable.trans
      (ih (fun z hz => hW z (List.mem_cons_of_mem _ hz)))
end Paper.Hypergraph
