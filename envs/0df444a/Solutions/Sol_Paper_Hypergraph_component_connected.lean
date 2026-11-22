-- Prove2me | solution 1 for Paper.Hypergraph.component_connected
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:56:48.522151+00:00
-- url     : https://prove2.me/submissions/abd8a8a0-0185-49dc-9a0e-65f42e3500a5

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
theorem _root_.solution (H : Hypergraph) {C : Finset ℕ} (hC : C ∈ H.components) :
    (H.induce C).Connected := by
  obtain ⟨hCV, a, ha, hreach⟩ := mem_filter.mp hC
  have hsub : C ⊆ H.vertices := mem_powerset.mp hCV
  have lift_walk : ∀ {u v : ℕ}, H.primal.Walk u v → u ∈ C →
      (H.induce C).primal.Reachable u v := by
    intro u v p
    induction p with
    | nil => intro _; exact .rfl
    | @cons u v z huv p ih =>
      intro hu
      obtain ⟨hne, e, he, hue, hve⟩ := huv
      have hvV := H.edge_subset e he hve
      have huv' : H.primal.Adj u v := ⟨hne, e, he, hue, hve⟩
      have hvC : v ∈ C := (hreach v hvV).mpr
        (((hreach u (hsub hu)).mp hu).trans huv'.reachable)
      exact ((H.primal_induce_adj C hu hvC).mpr huv').reachable.trans (ih hvC)
  refine ⟨⟨a, mem_inter.mpr ⟨hsub ha, ha⟩⟩, ?_⟩
  intro u hu v hv
  have huC := (mem_inter.mp hu).2
  have hvC := (mem_inter.mp hv).2
  obtain ⟨p⟩ := ((hreach u (hsub huC)).mp huC).symm.trans
    ((hreach v (hsub hvC)).mp hvC)
  exact lift_walk p huC
end Paper.Hypergraph
