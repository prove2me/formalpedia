-- Prove2me | solution 1 for VirialTheorem.virial_sum_pairs
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T06:06:59.917435+00:00
-- url     : https://prove2.me/submissions/95811f03-317d-4126-be78-2d9ac783dd0c

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
set_option autoImplicit false

theorem solution {N : ℕ} (Fp : Fin N → Fin N → EuclideanSpace ℝ (Fin 3))
    (x : Fin N → EuclideanSpace ℝ (Fin 3))
    (hanti : ∀ j k, Fp j k = -Fp k j) :
    ∑ k, inner ℝ (∑ j, Fp j k) (x k) =
      ∑ k, ∑ j ∈ Finset.univ.filter (fun j => j < k), inner ℝ (Fp j k) (x k - x j) := by
  classical
  have hdiag (k : Fin N) : Fp k k = 0 := by
    ext i
    have h := congrArg (fun v : EuclideanSpace ℝ (Fin 3) => v i) (hanti k k)
    change Fp k k i = -(Fp k k i) at h
    change Fp k k i = 0
    linarith
  let g (j k : Fin N) : ℝ := inner ℝ (Fp j k) (x k)
  have hsplit (j k : Fin N) : g j k =
      (if j < k then g j k else 0) + (if k < j then g j k else 0) := by
    rcases lt_trichotomy j k with h | h | h
    · simp [h, not_lt.mpr h.le]
    · subst k; simp [g, hdiag]
    · simp [h, not_lt.mpr h.le]
  have hswap : (∑ k, ∑ j, if k < j then g j k else 0) =
      ∑ k, ∑ j, if j < k then g k j else 0 := by
    exact Finset.sum_comm
  have hpair (j k : Fin N) : g j k + g k j = inner ℝ (Fp j k) (x k - x j) := by
    dsimp [g]
    rw [hanti k j, inner_neg_left, inner_sub_right]
    ring
  calc
    ∑ k, inner ℝ (∑ j, Fp j k) (x k) = ∑ k, ∑ j, g j k := by
      simp only [g, sum_inner]
    _ = ∑ k, ∑ j, ((if j < k then g j k else 0) + (if k < j then g j k else 0)) := by
      apply Finset.sum_congr rfl
      intro k _
      exact Finset.sum_congr rfl (fun j _ => hsplit j k)
    _ = (∑ k, ∑ j, if j < k then g j k else 0) +
        (∑ k, ∑ j, if k < j then g j k else 0) := by simp only [Finset.sum_add_distrib]
    _ = (∑ k, ∑ j, if j < k then g j k else 0) +
        (∑ k, ∑ j, if j < k then g k j else 0) := by rw [hswap]
    _ = ∑ k, ∑ j ∈ Finset.univ.filter (fun j => j < k), inner ℝ (Fp j k) (x k - x j) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k _
      rw [← Finset.sum_add_distrib, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro j _
      by_cases h : j < k
      · simp only [if_pos h, hpair]
      · simp [h]
