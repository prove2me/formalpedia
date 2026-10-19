-- Prove2me | solution 1 for SoficGroups.almostCentralizerGap_of_expansion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:53.013021+00:00
-- url     : https://prove2.me/submissions/c4a4332c-4301-4117-a87b-aae8b4990823

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_hamming_dichotomy_of_expansion

set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
universe u v w
open scoped Pointwise commutatorElement symmDiff
namespace SoficGroups
theorem _root_.solution {V ι : Type*}
    [Fintype V] [Fintype ι] [DecidableEq V]
    (σ : ι → Equiv.Perm V) (tolerance : ℕ) (h : ℝ)
    (hpositive : 0 < h)
    (hexp : ∀ A : Finset V,
      h * min (A.card : ℝ)
          ((Fintype.card V : ℝ) - A.card) ≤ (boundary σ A : ℝ))
    (hsmall : (10 : ℝ) * tolerance < h * Fintype.card V) :
    AlmostCentralizerGap σ tolerance := by
  constructor
  intro p q
  have hdef :
      ((permutationCommutationDefect σ p.permutation +
        permutationCommutationDefect σ q.permutation : ℕ) : ℝ) ≤
          2 * (tolerance : ℝ) := by
    have hnat : permutationCommutationDefect σ p.permutation +
        permutationCommutationDefect σ q.permutation ≤ 2 * tolerance := by
      have hp := p.defect_le
      have hq := q.defect_le
      omega
    exact_mod_cast hnat
  rcases hamming_dichotomy_of_expansion σ h hexp p.permutation q.permutation with
    hnear | hfar
  · left
    by_contra hnot
    have hlarge : Fintype.card V <
        5 * permutationDistance p.permutation q.permutation :=
      Nat.lt_of_not_ge hnot
    have hlarge' : (Fintype.card V : ℝ) <
        5 * (permutationDistance p.permutation q.permutation : ℝ) := by
      exact_mod_cast hlarge
    have hpos : 0 < h *
        (5 * (permutationDistance p.permutation q.permutation : ℝ) -
          Fintype.card V) :=
      mul_pos hpositive (sub_pos.mpr hlarge')
    change h * (permutationDistance p.permutation q.permutation : ℝ) ≤ _
      at hnear
    nlinarith
  · right
    by_contra hnot
    have hlarge :
        5 * permutationDistance p.permutation q.permutation ≤
          4 * Fintype.card V := Nat.le_of_not_gt hnot
    have hlarge' :
        5 * (permutationDistance p.permutation q.permutation : ℝ) ≤
          4 * (Fintype.card V : ℝ) := by
      exact_mod_cast hlarge
    have hpos : 0 ≤ h *
        (4 * (Fintype.card V : ℝ) -
          5 * (permutationDistance p.permutation q.permutation : ℝ)) :=
      mul_nonneg hpositive.le (sub_nonneg.mpr hlarge')
    change h * ((Fintype.card V : ℝ) -
      permutationDistance p.permutation q.permutation) ≤ _ at hfar
    nlinarith
end SoficGroups
