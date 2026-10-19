-- Prove2me | solution 1 for SoficGroups.maximal_bad_cut_induced_lower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:50.999068+00:00
-- url     : https://prove2.me/submissions/d775131d-7b09-46bf-845e-e5cc28371f54

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_boundary_union_le

set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
universe u v w
open scoped Pointwise commutatorElement symmDiff
namespace SoficGroups
theorem _root_.solution {V ι : Type*}
    [Fintype V] [Fintype ι] [DecidableEq V]
    (σ : ι → Equiv.Perm V) (B E : Finset V) (ell : ℝ)
    (hB : (boundary σ B : ℝ) ≤ ell * (B.card : ℝ))
    (hmax : ∀ A : Finset V,
      2 * A.card ≤ Fintype.card V →
      (boundary σ A : ℝ) < ell * (A.card : ℝ) → A.card ≤ B.card)
    (hdisj : Disjoint B E) (hne : E.Nonempty)
    (hhalf : 2 * (B ∪ E).card ≤ Fintype.card V) :
    ell * (E.card : ℝ) ≤ (inducedBoundary σ B E : ℝ) := by
  classical
  by_contra h
  have hE : (inducedBoundary σ B E : ℝ) < ell * (E.card : ℝ) :=
    lt_of_not_ge h
  have hcut : (boundary σ (B ∪ E) : ℝ) ≤
      (boundary σ B : ℝ) + (inducedBoundary σ B E : ℝ) := by
    exact_mod_cast boundary_union_le σ B E
  have hcard : ((B ∪ E).card : ℝ) = (B.card : ℝ) + (E.card : ℝ) := by
    exact_mod_cast Finset.card_union_of_disjoint hdisj
  have hbad : (boundary σ (B ∪ E) : ℝ) < ell * ((B ∪ E).card : ℝ) := by
    rw [hcard]
    nlinarith
  have hsize := hmax (B ∪ E) hhalf hbad
  have hepos : 0 < E.card := Finset.card_pos.mpr hne
  have hnat := Finset.card_union_of_disjoint hdisj
  omega
end SoficGroups
