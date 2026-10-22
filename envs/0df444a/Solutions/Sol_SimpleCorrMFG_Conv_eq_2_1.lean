-- Prove2me | solution 1 for SimpleCorrMFG.Conv.eq_2_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T06:05:51.369393+00:00
-- url     : https://prove2.me/submissions/472e3380-3fb8-44f9-bed8-59efc22b8019

import Mathlib
import Definitions.Def_SimpleCorrMFG_Conv_Model

open MeasureTheory ProbabilityTheory unitInterval Filter Topology SimpleCorrMFG.Conv

lemma empOn_univ_apply {S : Type} [Fintype S] [DecidableEq S] [Nonempty S] {N : ℕ} (hN : 0 < N)
    (s : Fin N → S) (y : S) :
    (empOn Finset.univ s).1 y
      = (1 / (N : ℝ)) * ∑ i, (if s i = y then (1 : ℝ) else 0) := by
  have hne : (Finset.univ : Finset (Fin N)).Nonempty := Finset.univ_nonempty_iff.mpr ⟨⟨0, hN⟩⟩
  rw [empOn, dif_pos hne]
  show (∑ j ∈ Finset.univ, if s j = y then (1:ℝ) else 0) / ((Finset.univ : Finset (Fin N)).card : ℝ) = _
  rw [Finset.card_univ, Fintype.card_fin]
  ring

lemma empOn_univ_perm {S : Type} [Fintype S] [DecidableEq S] [Nonempty S] {N : ℕ} (hN : 0 < N)
    (s : Fin N → S) (π : Equiv.Perm (Fin N)) :
    empOn Finset.univ (s ∘ π) = empOn Finset.univ s := by
  apply Subtype.ext
  funext y
  show (empOn Finset.univ (s ∘ π)).1 y = (empOn Finset.univ s).1 y
  rw [empOn_univ_apply hN, empOn_univ_apply hN]
  congr 1
  exact Equiv.sum_comp π (fun i => if s i = y then (1 : ℝ) else 0)

lemma dist_le_mismatch {S : Type} [Fintype S] [DecidableEq S] [Nonempty S] {N : ℕ} (hN : 0 < N)
    (s s' : Fin N → S) :
    distTV (empOn Finset.univ s) (empOn Finset.univ s') ≤
      (1 / (N : ℝ)) * ∑ i, (if s i ≠ s' i then (1 : ℝ) else 0) := by
  unfold distTV
  show (1 / 2 : ℝ) * ∑ x, |(empOn Finset.univ s).1 x - (empOn Finset.univ s').1 x| ≤ _
  simp_rw [empOn_univ_apply hN]
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have key : ∀ y : S, |(1 / (N : ℝ)) * ∑ i, (if s i = y then (1 : ℝ) else 0) -
      (1 / (N : ℝ)) * ∑ i, (if s' i = y then (1 : ℝ) else 0)| ≤
      (1 / (N : ℝ)) * ∑ i, |(if s i = y then (1 : ℝ) else 0) - (if s' i = y then (1 : ℝ) else 0)| := by
    intro y
    rw [← mul_sub, ← Finset.sum_sub_distrib, abs_mul, abs_of_pos (by positivity)]
    gcongr
    exact Finset.abs_sum_le_sum_abs _ _
  have key2 : ∀ i : Fin N, ∑ y : S, |(if s i = y then (1 : ℝ) else 0) - (if s' i = y then (1 : ℝ) else 0)|
      = 2 * (if s i ≠ s' i then (1 : ℝ) else 0) := by
    intro i
    by_cases h : s i = s' i
    · simp [h]
    · simp only [ne_eq, h, not_false_eq_true, if_true]
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (s i)),
        ← Finset.sum_erase_add _ _ (Finset.mem_erase.mpr ⟨Ne.symm h, Finset.mem_univ (s' i)⟩)]
      rw [Finset.sum_eq_zero]
      · simp [h, Ne.symm h]; norm_num
      · intro y hy
        have h1 : y ≠ s' i := (Finset.mem_erase.mp hy).1
        have h2 : y ≠ s i := (Finset.mem_erase.mp (Finset.mem_erase.mp hy).2).1
        simp [Ne.symm h1, Ne.symm h2]
  calc (1 / 2 : ℝ) * ∑ y, |(1 / (N : ℝ)) * ∑ i, (if s i = y then (1 : ℝ) else 0) -
      (1 / (N : ℝ)) * ∑ i, (if s' i = y then (1 : ℝ) else 0)|
      ≤ (1 / 2 : ℝ) * ∑ y : S, (1 / (N : ℝ)) * ∑ i,
          |(if s i = y then (1 : ℝ) else 0) - (if s' i = y then (1 : ℝ) else 0)| := by
        gcongr with y; exact key y
    _ = (1 / (N : ℝ)) * ∑ i, (if s i ≠ s' i then (1 : ℝ) else 0) := by
        rw [← Finset.mul_sum, Finset.sum_comm]
        simp_rw [key2]
        rw [← Finset.mul_sum]; ring

theorem solution {S : Type} [Fintype S] [DecidableEq S] [Nonempty S] {N : ℕ} (hN : 0 < N)
    (s s' : Fin N → S) :
    distTV (empOn Finset.univ s) (empOn Finset.univ s') ≤
        ⨅ π : Equiv.Perm (Fin N), (1 / (N : ℝ)) * ∑ i, (if s i ≠ s' (π i) then (1 : ℝ) else 0) ∧
      (⨅ π : Equiv.Perm (Fin N), (1 / (N : ℝ)) * ∑ i, (if s i ≠ s' (π i) then (1 : ℝ) else 0)) ≤
        (1 / (N : ℝ)) * ∑ i, (if s i ≠ s' i then (1 : ℝ) else 0) := by
  constructor
  · apply le_ciInf
    intro π
    rw [← empOn_univ_perm hN s' π]
    exact dist_le_mismatch hN s (s' ∘ π)
  · have := ciInf_le (Set.finite_range (fun π : Equiv.Perm (Fin N) =>
      (1 / (N : ℝ)) * ∑ i, (if s i ≠ s' (π i) then (1 : ℝ) else 0))).bddBelow (1 : Equiv.Perm (Fin N))
    simp only [Equiv.Perm.coe_one, id_eq] at this
    exact this
