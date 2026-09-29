-- Prove2me | solution 1 for TraceEstimation.Gaussian.elementary_symmetric_bound
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T03:07:14.160007+00:00
-- url     : https://prove2.me/submissions/a0dcc124-9d44-4065-a2cc-cc9d3819bde3

import Mathlib
import Definitions.Def_TraceEstimation_Gaussian_hPoly

namespace TraceEstimation.Gaussian

theorem aux_esb_esymm_le {n : ℕ} (x : Fin n → ℝ) (hx : ∀ j, 0 ≤ x j) (s : Finset (Fin n)) :
    ∀ i : ℕ, ∑ S ∈ s.powersetCard i, ∏ j ∈ S, x j ≤ (∑ j ∈ s, x j) ^ i := by
  induction s using Finset.induction_on with
  | empty =>
    intro i
    cases i with
    | zero => simp
    | succ i =>
      rw [Finset.powersetCard_eq_empty.mpr (by simp)]
      simp
  | insert a s ha ih =>
    intro i
    cases i with
    | zero => simp
    | succ i =>
      have hsum_nonneg : 0 ≤ ∑ j ∈ s, x j := Finset.sum_nonneg (fun j _ => hx j)
      rw [Finset.powersetCard_succ_insert ha, Finset.sum_union, Finset.sum_image,
        Finset.sum_insert ha]
      · have h1 : ∑ S ∈ s.powersetCard i, ∏ j ∈ insert a S, x j
            = x a * ∑ S ∈ s.powersetCard i, ∏ j ∈ S, x j := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro S hS
          have haS : a ∉ S := fun h => ha ((Finset.mem_powersetCard.mp hS).1 h)
          rw [Finset.prod_insert haS]
        rw [h1]
        have hA := ih (i + 1)
        have hB := ih i
        have hpow : (∑ j ∈ s, x j) ^ i ≤ (x a + ∑ j ∈ s, x j) ^ i :=
          pow_le_pow_left₀ hsum_nonneg (by linarith [hx a]) i
        have hpn : 0 ≤ (∑ j ∈ s, x j) ^ i := pow_nonneg hsum_nonneg i
        calc ∑ S ∈ s.powersetCard (i + 1), ∏ j ∈ S, x j + x a * ∑ S ∈ s.powersetCard i, ∏ j ∈ S, x j
            ≤ (∑ j ∈ s, x j) ^ (i + 1) + x a * (∑ j ∈ s, x j) ^ i := by
              gcongr
              exact hx a
          _ = (∑ j ∈ s, x j) * (∑ j ∈ s, x j) ^ i + x a * (∑ j ∈ s, x j) ^ i := by ring
          _ ≤ (∑ j ∈ s, x j) * (x a + ∑ j ∈ s, x j) ^ i + x a * (x a + ∑ j ∈ s, x j) ^ i := by
              gcongr
              exact hx a
          _ = (x a + ∑ j ∈ s, x j) ^ (i + 1) := by ring
      · intro S hS T hT hST
        have haS : a ∉ S := fun h => ha ((Finset.mem_powersetCard.mp hS).1 h)
        have haT : a ∉ T := fun h => ha ((Finset.mem_powersetCard.mp hT).1 h)
        have := congrArg (fun U => U.erase a) hST
        simpa [Finset.erase_insert haS, Finset.erase_insert haT] using this
      · rw [Finset.disjoint_left]
        intro S hS hS'
        obtain ⟨T, _, rfl⟩ := Finset.mem_image.mp hS'
        exact ha ((Finset.mem_powersetCard.mp hS).1 (Finset.mem_insert_self a T))

end TraceEstimation.Gaussian

open TraceEstimation.Gaussian

theorem solution {n : ℕ} :
    (∀ x : Fin n → ℝ, (∀ j, 0 ≤ x j) → ∀ i : ℕ, 1 ≤ i → i ≤ n →
      ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard i, ∏ j ∈ S, x j ≤ (∑ j, x j) ^ i) ∧
    (∀ lam : Fin n → ℝ, (∀ j, 0 ≤ lam j) → ∀ t : ℝ, 0 ≤ t →
      |hPoly lam t| ≤ ∑ j ∈ Finset.Icc 2 n, (2 * (∑ k, lam k) * t) ^ j) := by
  refine ⟨fun x hx i _ _ => aux_esb_esymm_le x hx Finset.univ i, ?_⟩
  intro lam hlam t ht
  unfold hPoly
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  apply Finset.sum_le_sum
  intro s _
  have he0 : 0 ≤ ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard s, ∏ i ∈ S, lam i :=
    Finset.sum_nonneg (fun S _ => Finset.prod_nonneg (fun i _ => hlam i))
  have hle := aux_esb_esymm_le lam hlam Finset.univ s
  rw [abs_mul, abs_mul, abs_pow, abs_pow, abs_of_nonneg he0, abs_of_nonneg ht]
  rw [show (2 * (∑ k, lam k) * t) ^ s = |(-2 : ℝ)| ^ s * t ^ s * (∑ k, lam k) ^ s by
    rw [show |(-2 : ℝ)| = 2 by norm_num]; ring]
  gcongr
