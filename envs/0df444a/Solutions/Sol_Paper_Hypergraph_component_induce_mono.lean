-- Prove2me | solution 1 for Paper.Hypergraph.component_induce_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:09:39.463035+00:00
-- url     : https://prove2.me/submissions/c4b3836b-c3e7-4b0a-9c9f-b3cda28f58fb

import Definitions.Def_Paper_TrustBoundary
import Definitions.Def_Paper_Formalized
import Theorems.Thm_Paper_Hypergraph_component_mem_iff_reachable
import Theorems.Thm_Paper_Hypergraph_exists_component_of_mem
import Theorems.Thm_Paper_Hypergraph_primal_induce_mono

set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper
open Paper.Hypergraph
namespace Paper.Hypergraph
theorem _root_.solution (H : Hypergraph) {U W K : Finset ℕ} (hUW : U ⊆ W)
    (hK : K ∈ (H.induce U).components) :
    ∃ C ∈ (H.induce W).components, K ⊆ C := by
  have hsub := mem_powerset.mp (mem_filter.mp hK).1
  obtain ⟨v, hv, _⟩ := (mem_filter.mp hK).2
  have hvW : v ∈ (H.induce W).vertices :=
    mem_inter.mpr ⟨(mem_inter.mp (hsub hv)).1, hUW (mem_inter.mp (hsub hv)).2⟩
  obtain ⟨C, hC, hvC⟩ := (H.induce W).exists_component_of_mem hvW
  refine ⟨C, hC, ?_⟩
  intro z hz
  have hzW : z ∈ (H.induce W).vertices :=
    mem_inter.mpr ⟨(mem_inter.mp (hsub hz)).1, hUW (mem_inter.mp (hsub hz)).2⟩
  apply ((H.induce W).component_mem_iff_reachable hC hvC hzW).mpr
  have hh := ((H.induce U).component_mem_iff_reachable hK hv (hsub hz)).mp hz
  exact ⟨hh.some.mapLe (H.primal_induce_mono hUW)⟩
end Paper.Hypergraph
