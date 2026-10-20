-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P12.dissipationFunctional
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T00:45:09.339368+00:00
-- url     : https://prove2.me/submissions/fbdc38ea-732b-406d-b2a1-a55b9ae88270

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P12

noncomputable section

open scoped Matrix ComplexOrder Matrix.Norms.Frobenius

open Set

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Dependency50 QAlgorithms.Papers.Independent.Dependency50.P12

attribute [local instance 100] LieRing.ofAssociativeRing

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Dependency50.P12.Coordinates

open QAlgorithms.Papers.Independent.Information100

lemma g52a_single_l {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) (i j : Fin d) :
    (A * Matrix.single i j (1 : ℂ)) i j = A i i := by
  simp [Matrix.mul_apply, Matrix.single_apply]

lemma g52a_single_r {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) (i j : Fin d) :
    (Matrix.single i j (1 : ℂ) * A) i j = A j j := by
  simp [Matrix.mul_apply, Matrix.single_apply]

lemma g52a_single_lr {d : ℕ} (A B : Matrix (Fin d) (Fin d) ℂ) (i j : Fin d) :
    (A * Matrix.single i j (1 : ℂ) * B) i j = A i i * B j j := by
  rw [Matrix.mul_assoc, Matrix.mul_apply, Finset.sum_eq_single i]
  · congr 1
    rw [Matrix.mul_apply, Finset.sum_eq_single j]
    · simp
    · intro b _ hb; simp [Matrix.single_apply, Ne.symm hb]
    · simp
  · intro b _ hb
    have : (Matrix.single i j (1 : ℂ) * B) b j = 0 := by
      rw [Matrix.mul_apply]
      refine Finset.sum_eq_zero fun c _ => ?_
      simp [Matrix.single_apply, Ne.symm hb]
    rw [this, mul_zero]
  · simp

lemma g52a_sum3 {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (f : α → β → γ → ℂ) : ∑ a, ∑ b, ∑ c, f a b c = ∑ b, ∑ c, ∑ a, f a b c := by
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun b _ => Finset.sum_comm

lemma g52a_sum4 {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (f : α → β → γ → δ → ℂ) :
    ∑ a, ∑ b, ∑ c, ∑ e, f a b c e = ∑ c, ∑ e, ∑ a, ∑ b, f a b c e := by
  rw [Finset.sum_congr rfl fun a _ => g52a_sum3 (fun b c e => f a b c e)]
  exact g52a_sum3 (fun a c e => ∑ b, f a b c e)

lemma g52a_single_r2 {d : ℕ} (A B : Matrix (Fin d) (Fin d) ℂ) (i j : Fin d) :
    (Matrix.single i j (1 : ℂ) * A * B) i j = (A * B) j j := by
  rw [Matrix.mul_assoc, g52a_single_r]

lemma g52a_e1 {d : ℕ} (A B M : Matrix (Fin d) (Fin d) ℂ) (k : ℂ) (hA : A.trace = 0) :
    ∑ i, ∑ j, k * (A i i * B j j - 2⁻¹ * (M i i + M j j)) = -(d : ℂ) * (k * M.trace) := by
  have s1 : ∑ i, ∑ j, A i i * B j j = 0 := by
    rw [← Finset.sum_mul_sum]
    rw [show ∑ i, A i i = A.trace from rfl, hA, zero_mul]
  have s2 : ∑ i : Fin d, ∑ j : Fin d, M i i = d * M.trace := by
    simp [Matrix.trace, Finset.mul_sum]
  have s3 : ∑ i : Fin d, ∑ j : Fin d, M j j = d * M.trace := by
    rw [Finset.sum_comm]; exact s2
  have s1' : ∑ i, A i i * ∑ j, B j j = 0 := by
    rw [← Finset.sum_mul]
    rw [show ∑ i, A i i = A.trace from rfl, hA, zero_mul]
  have hpt : ∀ i j, k * (A i i * B j j - 2⁻¹ * (M i i + M j j)) =
      k * (A i i * B j j) - (k * 2⁻¹) * M i i - (k * 2⁻¹) * M j j := by intros; ring
  simp only [hpt, Finset.sum_sub_distrib, ← Finset.mul_sum, s1', s2, s3]
  ring

lemma g52a_superTrace_koss {d : ℕ}
    (F : Fin (d^2-1) → P59.Operator d) (hF : P59.IsTracelessHermitianBasis F)
    (H : P59.Operator d) (K : Matrix (Fin (d^2-1)) (Fin (d^2-1)) ℂ) :
    P59.superoperatorTrace (P59.kossakowskiAction F H K) =
      -(d : ℂ) * (K * P59.gramMatrix F).trace := by
  have hh : ∀ k, (F k)ᴴ = F k := fun k => (hF.1 k).1
  have ht : ∀ k, (F k).trace = 0 := fun k => (hF.1 k).2
  have hc : ∑ i : Fin d, ∑ j : Fin d, -Complex.I * (H i i - H j j) = 0 := by
    simp only [mul_sub, Finset.sum_sub_distrib]
    rw [sub_eq_zero, Finset.sum_comm]
  unfold P59.superoperatorTrace P59.kossakowskiAction P59.coherent
  simp only [Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply, Matrix.sub_apply,
    smul_eq_mul, Finset.sum_add_distrib, g52a_single_lr, g52a_single_r2, g52a_single_l,
    g52a_single_r, hh]
  rw [hc, zero_add, g52a_sum4]
  rw [Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    g52a_e1 (F a) (F b) (F b * F a) (K a b) (ht a)]
  have hG : (K * P59.gramMatrix F).trace = ∑ a, ∑ b, K a b * (F b * F a).trace := by
    have : ∀ a, (K * P59.gramMatrix F) a a = ∑ b, K a b * (F b * F a).trace := fun a => by
      rw [Matrix.mul_apply]
      exact Finset.sum_congr rfl fun b _ => by
        show K a b * (F a * F b).trace = K a b * (F b * F a).trace
        rw [Matrix.trace_mul_comm]
    exact Finset.sum_congr rfl fun a _ => this a
  rw [hG]
  simp only [Finset.mul_sum]

/-- arXiv:2608.27330v1, PDF p.12, Lemma 2.16.
K is Hermitian and may be indefinite; the superoperator trace is on all B(H). -/
theorem solution {d : ℕ} (hd : 0 < d)
    (F : Fin (d^2-1) → P59.Operator d) (hF : P59.IsTracelessHermitianBasis F)
    (H : P59.Operator d) (hH : H.IsHermitian)
    (K : Matrix (Fin (d^2-1)) (Fin (d^2-1)) ℂ) (hK : K.IsHermitian) :
    P59.superoperatorTrace (P59.kossakowskiAction F H K) =
      -(d : ℂ) * (K * P59.gramMatrix F).trace ∧
    (P59.gramMatrix F = 1 →
      P59.superoperatorTrace (P59.kossakowskiAction F H K) = -(d : ℂ) * K.trace) ∧
    (P59.gramMatrix F = 2 • (1 : Matrix (Fin (d^2-1)) (Fin (d^2-1)) ℂ) →
      P59.superoperatorTrace (P59.kossakowskiAction F H K) =
        -2 * (d : ℂ) * K.trace) := by
  have h1 := g52a_superTrace_koss F hF H K
  refine ⟨h1, fun hG => ?_, fun hG => ?_⟩
  · rw [h1, hG, Matrix.mul_one]
  · rw [h1, hG, Matrix.mul_smul, Matrix.mul_one, Matrix.trace_smul]
    simp only [nsmul_eq_mul, Nat.cast_ofNat]
    ring


end

