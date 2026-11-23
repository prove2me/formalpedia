-- Prove2me | solution 1 for SpectralContrastive.labels_cut_bound
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-23T21:18:19.664597+00:00
-- url     : https://prove2.me/submissions/c6c917fa-a636-4dbc-93a5-3f01f61e3c0f

import Mathlib
import Definitions.Def_SpectralContrastive_Basic

open Matrix
namespace SpectralContrastive

lemma lc_aux1 {Xbar X : Type*} [Fintype Xbar] [Fintype X] (P : Xbar → ℝ) (A : Xbar → X → ℝ)
    (S : X → X → ℝ) :
    ∑ xb, P xb * ∑ x, ∑ x', A xb x * A xb x' * S x x' =
      ∑ x, ∑ x', augWeight P A x x' * S x x' := by
  unfold augWeight
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun x' _ => Finset.sum_congr rfl fun xb _ => by ring
lemma lc_aux {X : Type*} [Fintype X] (a e : X → ℝ) (ha : ∑ x, a x = 1) :
    ∑ x, ∑ x', a x * a x' * (e x + e x') = 2 * ∑ x, a x * e x := by
  simp only [mul_add, Finset.sum_add_distrib]
  have h1 : ∑ x, ∑ x', a x * a x' * e x = ∑ x, a x * e x := by
    refine Finset.sum_congr rfl fun x _ => ?_
    calc ∑ x', a x * a x' * e x = ∑ x', (a x * e x) * a x' :=
          Finset.sum_congr rfl fun _ _ => by ring
      _ = a x * e x := by rw [← Finset.mul_sum, ha, mul_one]
  have h2 : ∑ x, ∑ x', a x * a x' * e x' = ∑ x, a x * e x := by
    calc _ = ∑ x, a x * ∑ x', a x' * e x' :=
          Finset.sum_congr rfl fun x _ => by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
      _ = _ := by rw [← Finset.sum_mul, ha, one_mul]
  rw [h1, h2]; ring

theorem labels_cut_bound {Xbar X : Type*} [Fintype Xbar] [Fintype X] [DecidableEq X] {r : ℕ}
    (P : Xbar → ℝ) (A : Xbar → X → ℝ) (hM : IsAugModel P A) (y : Xbar → Fin r) (α : ℝ)
    (g : X → Fin r) (hg : labelDisagree P A y g ≤ α) :
    ∃ yhat : X → Fin r, labelDisagree P A y yhat ≤ α ∧
      cutWeight (augWeight P A) yhat ≤ 2 * α := by
  obtain ⟨hP0, hP1, hA0, hA1, hsupp⟩ := hM
  refine ⟨g, hg, ?_⟩
  calc cutWeight (augWeight P A) g
      = ∑ xb, P xb * ∑ x, ∑ x', A xb x * A xb x' * (if g x ≠ g x' then (1:ℝ) else 0) := by
        rw [lc_aux1 P A (fun x x' => if g x ≠ g x' then (1:ℝ) else 0)]; rfl
    _ ≤ ∑ xb, P xb * ∑ x, ∑ x', A xb x * A xb x' *
          ((if g x ≠ y xb then (1:ℝ) else 0) + (if g x' ≠ y xb then (1:ℝ) else 0)) := by
        apply Finset.sum_le_sum; intro xb _
        apply mul_le_mul_of_nonneg_left _ (hP0 xb)
        apply Finset.sum_le_sum; intro x _
        apply Finset.sum_le_sum; intro x' _
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg (hA0 xb x) (hA0 xb x'))
        by_cases h2 : g x ≠ y xb
        · rw [if_pos h2]; split_ifs <;> norm_num
        · by_cases h3 : g x' ≠ y xb
          · rw [if_pos h3]; split_ifs <;> norm_num
          · push_neg at h2 h3
            simp [h2, h3]
    _ = ∑ xb, P xb * (2 * ∑ x, A xb x * (if g x ≠ y xb then (1:ℝ) else 0)) :=
        Finset.sum_congr rfl fun xb _ => by
          rw [lc_aux (A xb) (fun x => if g x ≠ y xb then (1:ℝ) else 0) (hA1 xb)]
    _ = 2 * labelDisagree P A y g := by
        unfold labelDisagree; rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun xb _ => by ring
    _ ≤ 2 * α := by linarith


end SpectralContrastive

open SpectralContrastive in
theorem solution {Xbar X : Type*} [Fintype Xbar] [Fintype X] [DecidableEq X] {r : ℕ}
    (P : Xbar → ℝ) (A : Xbar → X → ℝ) (hM : IsAugModel P A) (y : Xbar → Fin r) (α : ℝ)
    (g : X → Fin r) (hg : labelDisagree P A y g ≤ α) :
    ∃ yhat : X → Fin r, labelDisagree P A y yhat ≤ α ∧
      cutWeight (augWeight P A) yhat ≤ 2 * α := by
  obtain ⟨hP0, hP1, hA0, hA1, hsupp⟩ := hM
  refine ⟨g, hg, ?_⟩
  calc cutWeight (augWeight P A) g
      = ∑ xb, P xb * ∑ x, ∑ x', A xb x * A xb x' * (if g x ≠ g x' then (1:ℝ) else 0) := by
        rw [lc_aux1 P A (fun x x' => if g x ≠ g x' then (1:ℝ) else 0)]; rfl
    _ ≤ ∑ xb, P xb * ∑ x, ∑ x', A xb x * A xb x' *
          ((if g x ≠ y xb then (1:ℝ) else 0) + (if g x' ≠ y xb then (1:ℝ) else 0)) := by
        apply Finset.sum_le_sum; intro xb _
        apply mul_le_mul_of_nonneg_left _ (hP0 xb)
        apply Finset.sum_le_sum; intro x _
        apply Finset.sum_le_sum; intro x' _
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg (hA0 xb x) (hA0 xb x'))
        by_cases h2 : g x ≠ y xb
        · rw [if_pos h2]; split_ifs <;> norm_num
        · by_cases h3 : g x' ≠ y xb
          · rw [if_pos h3]; split_ifs <;> norm_num
          · push_neg at h2 h3
            simp [h2, h3]
    _ = ∑ xb, P xb * (2 * ∑ x, A xb x * (if g x ≠ y xb then (1:ℝ) else 0)) :=
        Finset.sum_congr rfl fun xb _ => by
          rw [lc_aux (A xb) (fun x => if g x ≠ y xb then (1:ℝ) else 0) (hA1 xb)]
    _ = 2 * labelDisagree P A y g := by
        unfold labelDisagree; rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun xb _ => by ring
    _ ≤ 2 * α := by linarith

