-- Prove2me | solution 1 for SoficGroups.disjoint_dominant_intersections_false
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:50.999068+00:00
-- url     : https://prove2.me/submissions/7453072e-8dee-41b3-9ed9-7c5ce90d46e9

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
universe u v w
open scoped Pointwise commutatorElement symmDiff
namespace SoficGroups
theorem _root_.solution {V : Type*} [DecidableEq V]
    (P Q D : Finset V) (hdisj : Disjoint P Q)
    (hP : D.card < 2 * (P ∩ D).card)
    (hQ : D.card < 2 * (Q ∩ D).card) : False := by
  have hparts : Disjoint (P ∩ D) (Q ∩ D) := by
    exact Finset.disjoint_of_subset_left (Finset.inter_subset_left)
      (Finset.disjoint_of_subset_right (Finset.inter_subset_left) hdisj)
  have hsub : (P ∩ D) ∪ (Q ∩ D) ⊆ D := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact (Finset.mem_inter.mp hx).2
    · exact (Finset.mem_inter.mp hx).2
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hparts] at hcard
  omega
end SoficGroups
