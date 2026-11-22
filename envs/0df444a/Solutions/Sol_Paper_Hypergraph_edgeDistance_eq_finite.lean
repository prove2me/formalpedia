-- Prove2me | solution 1 for Paper.Hypergraph.edgeDistance_eq_finite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:00:36.626053+00:00
-- url     : https://prove2.me/submissions/ba675b59-7481-4c58-89ab-90b8583c0662

import Definitions.Def_Paper_TrustBoundary
import Definitions.Def_Paper_Formalized
import Theorems.Thm_Paper_Hypergraph_walk_vertices
import Theorems.Thm_Paper_Hypergraph_vertexDistance_nonneg
import Theorems.Thm_Paper_Hypergraph_vertexDistance_le_option

set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper
open Paper.Hypergraph
namespace Paper.Hypergraph
theorem _root_.solution (H : Hypergraph) {x : ℕ → ℝ}
    (hx : ∀ v ∈ H.vertices, 0 ≤ x v) {e f : ℕ} (he : e ∈ H.edges) (hf : f ∈ H.edges) :
    H.edgeDistance x e f = H.finiteEdgeDistance e f x := by
  have hne : {r | ∃ u ∈ H.edge e, ∃ v ∈ H.edge f, r = H.vertexDistance x u v}.Nonempty := by
    obtain ⟨u, hu⟩ := H.edge_nonempty e he
    obtain ⟨v, hv⟩ := H.edge_nonempty f hf
    exact ⟨_, u, hu, v, hv, rfl⟩
  have hb : BddBelow {r | ∃ u ∈ H.edge e, ∃ v ∈ H.edge f, r = H.vertexDistance x u v} := by
    refine ⟨0, ?_⟩
    rintro r ⟨u, hu, v, hv, rfl⟩
    exact H.vertexDistance_nonneg hx (H.edge_subset e he hu)
  have hop {u v : ℕ} (hu : u ∈ H.edge e) (hv : v ∈ H.edge f)
      (p : H.primal.Walk u v) (hp : p.IsPath) :
      some p.support.toFinset ∈ H.separatorPathOptions e f := by
    apply mem_insert_of_mem
    apply mem_image.mpr
    refine ⟨p.support.toFinset, mem_filter.mpr ⟨mem_powerset.mpr ?_, u, hu, v, hv, p, hp, rfl⟩, rfl⟩
    intro z hz
    exact H.walk_vertices p (H.edge_subset e he hu) z (List.mem_toFinset.mp hz)
  apply le_antisymm
  · apply Finset.le_inf'
    intro o ho
    cases o with
    | none =>
      obtain ⟨u, hu⟩ := H.edge_nonempty e he
      obtain ⟨v, hv⟩ := H.edge_nonempty f hf
      exact (csInf_le hb ⟨u, hu, v, hv, rfl⟩).trans
        (H.vertexDistance_le_option hx (H.edge_subset e he hu) (Set.mem_insert 1 _))
    | some S =>
      have hh : ∃ u ∈ H.edge e, ∃ v ∈ H.edge f, ∃ p : H.primal.Walk u v,
          p.IsPath ∧ p.support.toFinset = S := by
        simp only [separatorPathOptions, mem_insert, Option.some_ne_none, false_or, mem_image, Option.some.injEq, exists_eq_right, mem_filter, mem_powerset] at ho
        exact ho.2
      obtain ⟨u, hu, v, hv, p, hp, rfl⟩ := hh
      exact (csInf_le hb ⟨u, hu, v, hv, rfl⟩).trans
        (H.vertexDistance_le_option hx (H.edge_subset e he hu) (Set.mem_insert_of_mem 1 ⟨p, hp, rfl⟩))
  · refine le_csInf hne ?_
    rintro r ⟨u, hu, v, hv, rfl⟩
    refine le_csInf ⟨1, Set.mem_insert _ _⟩ ?_
    rintro r (rfl | ⟨p, hp, rfl⟩)
    · exact Finset.inf'_le (fun o => pathOptionCost o x) (mem_insert_self none _)
    · exact Finset.inf'_le _ (hop hu hv p hp)
end Paper.Hypergraph
