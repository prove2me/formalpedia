-- Prove2me | solution 1 for SpectralContrastive.spectral_contrastive_loss_eq_mf
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-23T21:16:49.894047+00:00
-- url     : https://prove2.me/submissions/8fc90867-8bd7-4d4d-806a-c84790863a9b

import Mathlib
import Definitions.Def_SpectralContrastive_Basic

open Matrix
namespace SpectralContrastive

lemma sc_perm4 {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (g : α → β → γ → δ → ℝ) :
    ∑ a, ∑ b, ∑ c, ∑ d, g a b c d = ∑ c, ∑ d, ∑ a, ∑ b, g a b c d := by
  calc _ = ∑ a, ∑ c, ∑ d, ∑ b, g a b c d :=
        Finset.sum_congr rfl fun a _ => by
          rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun c _ => Finset.sum_comm
    _ = ∑ c, ∑ a, ∑ d, ∑ b, g a b c d := Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun c _ => Finset.sum_comm
lemma sc_aux1 {Xbar X : Type*} [Fintype Xbar] [Fintype X] (P : Xbar → ℝ) (A : Xbar → X → ℝ)
    (S : X → X → ℝ) :
    ∑ xb, P xb * ∑ x, ∑ x', A xb x * A xb x' * S x x' =
      ∑ x, ∑ x', augWeight P A x x' * S x x' := by
  unfold augWeight
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun x' _ => Finset.sum_congr rfl fun xb _ => by ring
lemma sc_aux2 {Xbar X : Type*} [Fintype Xbar] [Fintype X] (P : Xbar → ℝ) (A : Xbar → X → ℝ)
    (T : X → X → ℝ) :
    ∑ xb, ∑ xb', P xb * P xb' * ∑ x, ∑ x', A xb x * A xb' x' * T x x' =
      ∑ x, ∑ x', (∑ xb, P xb * A xb x) * (∑ xb, P xb * A xb x') * T x x' := by
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [sc_perm4 (fun a b c d => P a * P b * (A a c * A b d * T c d))]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
lemma sc_comb {X : Type*} [Fintype X] (a b c : X → X → ℝ) :
    ∑ x, ∑ x', (a x x' - 2 * b x x' + c x x') =
      -2 * (∑ x, ∑ x', b x x') + ∑ x, ∑ x', c x x' + ∑ x, ∑ x', a x x' := by
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]; ring
lemma sc_mf {X : Type*} [Fintype X] {k : ℕ} (w : X → X → ℝ) (hd : ∀ x, 0 < degree w x)
    (f : X → Fin k → ℝ) :
    mfLoss w (fun x i => Real.sqrt (degree w x) * f x i) =
      ∑ x, ∑ x', ((w x x') ^ 2 / (degree w x * degree w x') -
        2 * (w x x' * ∑ i, f x i * f x' i) +
        degree w x * degree w x' * (∑ i, f x i * f x' i) ^ 2) := by
  simp only [mfLoss, normAdj]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun x' _ => ?_
  have hp : 0 < degree w x * degree w x' := mul_pos (hd x) (hd x')
  have h1 : ∑ i, Real.sqrt (degree w x) * f x i * (Real.sqrt (degree w x') * f x' i) =
      Real.sqrt (degree w x * degree w x') * ∑ i, f x i * f x' i := by
    rw [Real.sqrt_mul (hd x).le, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [h1]
  have hs : Real.sqrt (degree w x * degree w x') ^ 2 = degree w x * degree w x' :=
    Real.sq_sqrt hp.le
  have hsp : 0 < Real.sqrt (degree w x * degree w x') := Real.sqrt_pos.mpr hp
  have e : w x x' / Real.sqrt (degree w x * degree w x') * Real.sqrt (degree w x * degree w x') = w x x' :=
    div_mul_cancel₀ _ hsp.ne'
  rw [sub_sq, div_pow, mul_pow, hs]
  linear_combination (-2 * ∑ i, f x i * f x' i) * e

theorem spectral_contrastive_loss_eq_mf {Xbar X : Type*} [Fintype Xbar] [Fintype X]
    [DecidableEq X] {k : ℕ} (P : Xbar → ℝ) (A : Xbar → X → ℝ) (hM : IsAugModel P A) :
    ∃ c : ℝ, ∀ f : X → Fin k → ℝ,
      mfLoss (augWeight P A) (fun x i => Real.sqrt (degree (augWeight P A) x) * f x i) =
        scLoss P A f + c := by
  obtain ⟨hP0, hP1, hA0, hA1, hsupp⟩ := hM
  have hdeg : ∀ x, degree (augWeight P A) x = ∑ xb, P xb * A xb x := by
    intro x; unfold degree augWeight; rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun xb _ => by rw [← Finset.mul_sum, hA1, mul_one]
  have hdpos : ∀ x, 0 < degree (augWeight P A) x := by
    intro x; rw [hdeg]
    obtain ⟨xb, hp, ha⟩ := hsupp x
    exact lt_of_lt_of_le (mul_pos hp ha) (Finset.single_le_sum (f := fun xb => P xb * A xb x)
      (fun i _ => mul_nonneg (hP0 i) (hA0 i x)) (Finset.mem_univ xb))
  refine ⟨∑ x, ∑ x', (augWeight P A x x') ^ 2 /
    (degree (augWeight P A) x * degree (augWeight P A) x'), fun f => ?_⟩
  rw [sc_mf _ hdpos, sc_comb]
  unfold scLoss
  rw [sc_aux1 P A (fun x x' => ∑ i, f x i * f x' i),
    sc_aux2 P A (fun x x' => (∑ i, f x i * f x' i) ^ 2)]
  simp only [← hdeg]


end SpectralContrastive

open SpectralContrastive in
theorem solution {Xbar X : Type*} [Fintype Xbar] [Fintype X]
    [DecidableEq X] {k : ℕ} (P : Xbar → ℝ) (A : Xbar → X → ℝ) (hM : IsAugModel P A) :
    ∃ c : ℝ, ∀ f : X → Fin k → ℝ,
      mfLoss (augWeight P A) (fun x i => Real.sqrt (degree (augWeight P A) x) * f x i) =
        scLoss P A f + c := by
  obtain ⟨hP0, hP1, hA0, hA1, hsupp⟩ := hM
  have hdeg : ∀ x, degree (augWeight P A) x = ∑ xb, P xb * A xb x := by
    intro x; unfold degree augWeight; rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun xb _ => by rw [← Finset.mul_sum, hA1, mul_one]
  have hdpos : ∀ x, 0 < degree (augWeight P A) x := by
    intro x; rw [hdeg]
    obtain ⟨xb, hp, ha⟩ := hsupp x
    exact lt_of_lt_of_le (mul_pos hp ha) (Finset.single_le_sum (f := fun xb => P xb * A xb x)
      (fun i _ => mul_nonneg (hP0 i) (hA0 i x)) (Finset.mem_univ xb))
  refine ⟨∑ x, ∑ x', (augWeight P A x x') ^ 2 /
    (degree (augWeight P A) x * degree (augWeight P A) x'), fun f => ?_⟩
  rw [sc_mf _ hdpos, sc_comb]
  unfold scLoss
  rw [sc_aux1 P A (fun x x' => ∑ i, f x i * f x' i),
    sc_aux2 P A (fun x x' => (∑ i, f x i * f x' i) ^ 2)]
  simp only [← hdeg]

