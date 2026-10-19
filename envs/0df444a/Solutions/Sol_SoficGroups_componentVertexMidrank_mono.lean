-- Prove2me | solution 1 for SoficGroups.componentVertexMidrank_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:52.29415+00:00
-- url     : https://prove2.me/submissions/7fe7d91a-7c37-4c11-a44b-08a15468c4c8

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
    (C : Finset V) (b : V → ℤ) {x y : V}
    (hxy : b x ≤ b y) :
    componentVertexMidrank C b x ≤ componentVertexMidrank C b y := by
  classical
  rcases C.eq_empty_or_nonempty with rfl | hC
  · simp [componentVertexMidrank]
  · have hc : 0 < (C.card : ℝ) := by
      exact_mod_cast Finset.card_pos.mpr hC
    rcases hxy.eq_or_lt with heq | hlt
    · unfold componentVertexMidrank
      simp [heq]
    · have hdisj := component_lower_equal_disjoint C b x
      have hsub :
          (C.filter fun z => b z < b x) ∪
            (C.filter fun z => b z = b x) ⊆
              C.filter fun z => b z < b y := by
        intro z hz
        rcases Finset.mem_union.mp hz with hz | hz
        · obtain ⟨hzC, hzx⟩ := Finset.mem_filter.mp hz
          exact Finset.mem_filter.mpr ⟨hzC, lt_trans hzx hlt⟩
        · obtain ⟨hzC, hzx⟩ := Finset.mem_filter.mp hz
          exact Finset.mem_filter.mpr ⟨hzC, hzx.symm ▸ hlt⟩
      have hcard := Finset.card_le_card hsub
      rw [Finset.card_union_of_disjoint hdisj] at hcard
      have hcard' :
          ((C.filter fun z => b z < b x).card : ℝ) +
            ((C.filter fun z => b z = b x).card : ℝ) ≤
              ((C.filter fun z => b z < b y).card : ℝ) := by
        exact_mod_cast hcard
      have hex : 0 ≤ ((C.filter fun z => b z = b x).card : ℝ) := by
        positivity
      have hey : 0 ≤ ((C.filter fun z => b z = b y).card : ℝ) := by
        positivity
      unfold componentVertexMidrank
      apply (div_le_div_iff_of_pos_right hc).2
      linarith
end SoficGroups
