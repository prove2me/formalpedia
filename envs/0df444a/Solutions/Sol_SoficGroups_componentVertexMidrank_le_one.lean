-- Prove2me | solution 1 for SoficGroups.componentVertexMidrank_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:52.29415+00:00
-- url     : https://prove2.me/submissions/bd831904-4805-4a2a-9b0b-739946f384c9

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_component_lower_equal_disjoint

set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
universe u v w
open scoped Pointwise commutatorElement symmDiff
namespace SoficGroups
theorem _root_.solution {V : Type*}
    (C : Finset V) (b : V → ℤ) (x : V) :
    componentVertexMidrank C b x ≤ 1 := by
  classical
  rcases C.eq_empty_or_nonempty with rfl | hC
  · simp [componentVertexMidrank]
  · have hc : 0 < (C.card : ℝ) := by
      exact_mod_cast Finset.card_pos.mpr hC
    have hdisj := component_lower_equal_disjoint C b x
    have hsub :
        (C.filter fun z => b z < b x) ∪
          (C.filter fun z => b z = b x) ⊆ C := by
      intro z hz
      rcases Finset.mem_union.mp hz with hz | hz
      · exact (Finset.mem_filter.mp hz).1
      · exact (Finset.mem_filter.mp hz).1
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hdisj] at hcard
    have hcard' :
        ((C.filter fun z => b z < b x).card : ℝ) +
          ((C.filter fun z => b z = b x).card : ℝ) ≤
            (C.card : ℝ) := by
      exact_mod_cast hcard
    unfold componentVertexMidrank
    apply (div_le_one hc).2
    have heq : 0 ≤ ((C.filter fun z => b z = b x).card : ℝ) := by
      positivity
    linarith
end SoficGroups
