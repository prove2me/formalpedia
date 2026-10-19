-- Prove2me | solution 1 for SoficGroups.prune_permutation_multigraph
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:50.999068+00:00
-- url     : https://prove2.me/submissions/2c523f22-225d-46e0-9454-1f4b30982c00

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_boundary_le_induced_add_deleted
import Theorems.Thm_SoficGroups_maximal_bad_cut_induced_lower
import Theorems.Thm_SoficGroups_large_cut_lower

set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
universe u v w
open scoped Pointwise commutatorElement symmDiff
namespace SoficGroups
theorem _root_.solution {V ι : Type*}
    [Fintype V] [Fintype ι] [DecidableEq V]
    (σ : ι → Equiv.Perm V) (γ ell a : ℝ) (B : Finset V)
    (hgap : ell < γ)
    (hadd : ∀ A : Finset V,
      γ * min (A.card : ℝ) ((Fintype.card V : ℝ) - (A.card : ℝ)) -
          a * (Fintype.card V : ℝ) ≤ (boundary σ A : ℝ))
    (hBhalf : 2 * B.card ≤ Fintype.card V)
    (hB : (boundary σ B : ℝ) ≤ ell * (B.card : ℝ))
    (hmax : ∀ A : Finset V,
      2 * A.card ≤ Fintype.card V →
      (boundary σ A : ℝ) < ell * (A.card : ℝ) → A.card ≤ B.card)
    (hsmall :
      2 * a * (2 * (γ - ell) + (Fintype.card ι : ℝ)) ≤ (γ - ell) ^ 2)
    (E : Finset V) (hdisj : Disjoint B E)
    (hEhalf : 2 * E.card ≤ Fintype.card V - B.card) :
    ell * (E.card : ℝ) ≤ (inducedBoundary σ B E : ℝ) := by
  classical
  rcases E.eq_empty_or_nonempty with rfl | hne
  · simp [inducedBoundary]
  by_cases hunion : 2 * (B ∪ E).card ≤ Fintype.card V
  · exact maximal_bad_cut_induced_lower σ B E ell hB hmax hdisj hne hunion
  have hBhalfReal :
      (B.card : ℝ) ≤ (Fintype.card V : ℝ) - (B.card : ℝ) := by
    have hcast : 2 * (B.card : ℝ) ≤ (Fintype.card V : ℝ) := by
      exact_mod_cast hBhalf
    linarith
  have haddB := hadd B
  rw [min_eq_left hBhalfReal] at haddB
  have hdeleted :
      (γ - ell) * (B.card : ℝ) ≤ a * (Fintype.card V : ℝ) := by
    linarith
  have hEhalfNat : 2 * E.card ≤ Fintype.card V :=
    hEhalf.trans (Nat.sub_le _ _)
  have hEhalfReal :
      (E.card : ℝ) ≤ (Fintype.card V : ℝ) - (E.card : ℝ) := by
    have hcast : 2 * (E.card : ℝ) ≤ (Fintype.card V : ℝ) := by
      exact_mod_cast hEhalfNat
    linarith
  have haddE := hadd E
  rw [min_eq_left hEhalfReal] at haddE
  have hremoval :
      (boundary σ E : ℝ) ≤ (inducedBoundary σ B E : ℝ) +
        (Fintype.card ι : ℝ) * (B.card : ℝ) := by
    exact_mod_cast boundary_le_induced_add_deleted σ B E
  have hcut :
      γ * (E.card : ℝ) - a * (Fintype.card V : ℝ) -
        (Fintype.card ι : ℝ) * (B.card : ℝ) ≤
        (inducedBoundary σ B E : ℝ) := by
    linarith
  have hcard := Finset.card_union_of_disjoint hdisj
  have hlargeNat : Fintype.card V < 2 * (B.card + E.card) := by
    simpa [hcard] using Nat.lt_of_not_ge hunion
  have hlargeCast :
      (Fintype.card V : ℝ) < 2 * ((B.card : ℝ) + (E.card : ℝ)) := by
    exact_mod_cast hlargeNat
  have hlarge :
      (Fintype.card V : ℝ) / 2 - (B.card : ℝ) < (E.card : ℝ) := by
    linarith
  exact large_cut_lower hgap (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    hdeleted hsmall hlarge hcut
end SoficGroups
