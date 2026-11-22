-- Prove2me | solution 1 for Paper.Hypergraph.vertexDistance_indicator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:07:07.444592+00:00
-- url     : https://prove2.me/submissions/6c6c12e8-d6e2-43cd-b348-f6caa702ed36

import Definitions.Def_Paper_TrustBoundary
import Definitions.Def_Paper_Formalized
import Theorems.Thm_Paper_Hypergraph_walk_vertices
import Theorems.Thm_Paper_Hypergraph_walk_reachable_induce
import Theorems.Thm_Paper_Hypergraph_primal_induce_le

set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper
open Paper.Hypergraph
namespace Paper.Hypergraph
theorem _root_.solution (H : Hypergraph) (S : Finset ℕ) {u v : ℕ}
    (hu : u ∈ H.vertices) (_hv : v ∈ H.vertices) :
    H.vertexDistance (indicator S) u v =
      if u ∉ S ∧ v ∉ S ∧ (H.induce (H.vertices \ S)).primal.Reachable u v
      then 0 else 1 := by
  have hnonneg : ∀ z, 0 ≤ indicator S z := by intro z; simp [indicator]; split_ifs <;> norm_num
  let costs : Set ℝ := insert 1 {r | ∃ p : H.primal.Walk u v, p.IsPath ∧
    r = ∑ z ∈ p.support.toFinset, indicator S z}
  have hne : costs.Nonempty := ⟨1, Set.mem_insert _ _⟩
  have hlo : ∀ r ∈ costs, 0 ≤ r := by
    rintro r (rfl | ⟨p, hp, rfl⟩)
    · norm_num
    · exact sum_nonneg (fun z _ => hnonneg z)
  have hbd : BddBelow costs := ⟨0, hlo⟩
  change sInf costs = _
  split_ifs with hh
  · obtain ⟨huS, hvS, hr⟩ := hh
    obtain ⟨p, hp⟩ := hr.exists_isPath
    have huJ : u ∈ (H.induce (H.vertices \ S)).vertices :=
      mem_inter.mpr ⟨hu, mem_sdiff.mpr ⟨hu, huS⟩⟩
    have hzsum : (∑ z ∈ (p.mapLe (H.primal_induce_le _)).support.toFinset,
        indicator S z) = 0 := by
      rw [SimpleGraph.Walk.support_mapLe_eq_support]
      apply sum_eq_zero
      intro z hz
      have hzJ := (H.induce (H.vertices \ S)).walk_vertices p huJ z (List.mem_toFinset.mp hz)
      exact if_neg (mem_sdiff.mp (mem_inter.mp hzJ).2).2
    apply le_antisymm
    · exact csInf_le hbd (Set.mem_insert_of_mem 1
        ⟨p.mapLe (H.primal_induce_le _), hp.mapLe _, hzsum.symm⟩)
    · exact le_csInf hne hlo
  · apply le_antisymm
    · exact csInf_le hbd (Set.mem_insert _ _)
    · refine le_csInf hne ?_
      rintro r (rfl | ⟨p, hp, rfl⟩)
      · exact le_rfl
      · by_contra hlt
        have hav : ∀ z ∈ p.support, z ∉ S := by
          intro z hz hzS
          have hsingle := single_le_sum (fun z _ => hnonneg z) (List.mem_toFinset.mpr hz)
          rw [indicator, if_pos hzS] at hsingle
          exact hlt hsingle
        apply hh
        refine ⟨hav u p.start_mem_support, hav v p.end_mem_support, ?_⟩
        exact H.walk_reachable_induce p (fun z hz =>
          mem_sdiff.mpr ⟨H.walk_vertices p hu z hz, hav z hz⟩)
end Paper.Hypergraph
