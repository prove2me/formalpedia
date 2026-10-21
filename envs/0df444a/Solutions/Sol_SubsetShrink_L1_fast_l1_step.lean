-- Prove2me | solution 1 for SubsetShrink.L1.fast_l1_step
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T03:50:36.914576+00:00
-- url     : https://prove2.me/submissions/ecc64b1c-0d1a-4695-b203-87a6e3d648ca

import Mathlib
import Definitions.Def_SubsetShrink_L1_Model

set_option autoImplicit false
open SubsetShrink.L1

theorem solution {p : ℕ} (k : ℕ) (lam : ℝ)
    (βhat β : Fin p → ℝ) (hlam : 0 ≤ lam)
    (hβ : SubsetShrink.Events.l0 β ≤ k) (hhat : SubsetShrink.Events.l0 βhat ≤ k) :
    lam * SubsetShrink.Events.l1 β - lam * SubsetShrink.Events.l1 βhat ≤ lam * SubsetShrink.Events.l1 (β - βhat) ∧
    lam * SubsetShrink.Events.l1 (β - βhat) ≤
      lam * Real.sqrt (2 * (k : ℝ)) * SubsetShrink.Events.l2 (β - βhat) := by
  constructor
  · have : SubsetShrink.Events.l1 β ≤ SubsetShrink.Events.l1 (β - βhat) + SubsetShrink.Events.l1 βhat := by
      unfold SubsetShrink.Events.l1
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro i _
      simp only [Pi.sub_apply]
      calc |β i| = |(β i - βhat i) + βhat i| := by ring_nf
        _ ≤ _ := abs_add_le _ _
    nlinarith
  · rw [mul_assoc]
    apply mul_le_mul_of_nonneg_left _ hlam
    set d : Fin p → ℝ := β - βhat with hd
    set S : Finset (Fin p) := Finset.univ.filter (fun i => d i ≠ 0) with hS
    have hSc : S.card ≤ 2 * k := by
      have hsub : S ⊆ Finset.univ.filter (fun i => β i ≠ 0) ∪ Finset.univ.filter (fun i => βhat i ≠ 0) := by
        intro i hi
        simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and, hd, Pi.sub_apply] at hi
        simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
        by_contra hc
        push_neg at hc
        apply hi
        rw [hc.1, hc.2]; ring
      calc S.card ≤ _ := Finset.card_le_card hsub
        _ ≤ _ := Finset.card_union_le _ _
        _ ≤ k + k := by
          apply add_le_add
          · exact hβ
          · exact hhat
        _ = 2 * k := by ring
    have h1 : SubsetShrink.Events.l1 d = ∑ i ∈ S, |d i| := by
      unfold SubsetShrink.Events.l1
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro i _ hi
      simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hi
      simp [hi]
    have h2 : ∑ i, d i ^ 2 = ∑ i ∈ S, d i ^ 2 := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro i _ hi
      simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hi
      simp [hi]
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq S (fun _ => (1:ℝ)) (fun i => |d i|)
    simp only [one_mul, one_pow, sq_abs, Finset.sum_const, nsmul_eq_mul, mul_one] at hcs
    unfold SubsetShrink.Events.l2
    rw [← Real.sqrt_mul (by positivity)]
    rw [h1]
    apply Real.le_sqrt_of_sq_le
    rw [h2]
    calc (∑ i ∈ S, |d i|) ^ 2 ≤ (S.card : ℝ) * ∑ i ∈ S, d i ^ 2 := hcs
      _ ≤ 2 * (k : ℝ) * ∑ i ∈ S, d i ^ 2 := by
        apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg (fun i _ => sq_nonneg _))
        have : (S.card : ℝ) ≤ ((2 * k : ℕ) : ℝ) := by exact_mod_cast hSc
        simpa using this
