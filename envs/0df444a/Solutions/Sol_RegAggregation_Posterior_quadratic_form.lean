-- Prove2me | solution 1 for RegAggregation.Posterior.quadratic_form
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T23:21:41.485866+00:00
-- url     : https://prove2.me/submissions/ad6f570f-668f-4a81-8392-45a25a08612b

import Mathlib
import Definitions.Def_RegAggregation_Posterior_Model

open Matrix

namespace RegAggMatAux

/-- all-ones matrix -/
noncomputable def J (K : ℕ) : Matrix (Fin K) (Fin K) ℝ := Matrix.of (fun _ _ => (1 : ℝ))

lemma J_mul_J (K : ℕ) : J K * J K = (K : ℝ) • J K := by
  ext i j
  simp [J, Matrix.mul_apply]

lemma cs_mul (K : ℕ) (A B C D : ℝ) :
    (A • (1 : Matrix (Fin K) (Fin K) ℝ) + B • J K) * (C • 1 + D • J K) =
      (A * C) • (1 : Matrix (Fin K) (Fin K) ℝ) + (A * D + B * C + B * D * K) • J K := by
  simp only [add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
    Matrix.mul_one, J_mul_J, smul_smul, add_smul]
  abel_nf
  module

lemma cs_inv (K : ℕ) (A B : ℝ) (hA : A ≠ 0) (hAB : A + K * B ≠ 0) :
    (A • (1 : Matrix (Fin K) (Fin K) ℝ) + B • J K)⁻¹ =
      (1 / A) • (1 : Matrix (Fin K) (Fin K) ℝ) + (-(B / (A * (A + K * B)))) • J K := by
  apply Matrix.inv_eq_right_inv
  rw [cs_mul]
  have h1 : A * (1 / A) = 1 := by field_simp
  have h2 : A * -(B / (A * (A + K * B))) + B * (1 / A) +
      B * -(B / (A * (A + K * B))) * K = 0 := by
    have hX : (A + K * B) * (A + K * B)⁻¹ = 1 := mul_inv_cancel₀ hAB
    have hY : A * A⁻¹ = 1 := mul_inv_cancel₀ hA
    rw [div_eq_mul_inv, div_eq_mul_inv, mul_inv]
    linear_combination (-B * A⁻¹) * hX
  rw [h1, h2]
  simp

lemma J_eq (K : ℕ) : J K = replicateCol (Fin 1) (fun _ : Fin K => (1 : ℝ)) *
    replicateRow (Fin 1) (fun _ : Fin K => (1 : ℝ)) := by
  ext i j
  simp [J, Matrix.mul_apply]

lemma cs_det (K : ℕ) (A B : ℝ) (hA : A ≠ 0) (hK : 1 ≤ K) :
    (A • (1 : Matrix (Fin K) (Fin K) ℝ) + B • J K).det = A ^ (K - 1) * (A + K * B) := by
  have : A • (1 : Matrix (Fin K) (Fin K) ℝ) + B • J K =
      A • (1 + replicateCol (Fin 1) (fun _ : Fin K => B / A) *
        replicateRow (Fin 1) (fun _ : Fin K => (1 : ℝ))) := by
    rw [smul_add, J_eq]
    congr 1
    ext i j
    simp [Matrix.mul_apply]
    field_simp
  rw [this, Matrix.det_smul]
  erw [det_one_add_replicateCol_mul_replicateRow]
  simp only [dotProduct, one_mul, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  obtain ⟨n, rfl⟩ : ∃ n, K = n + 1 := ⟨K - 1, by omega⟩
  simp only [Nat.add_sub_cancel, pow_succ]
  field_simp

lemma cs_quad (K : ℕ) (A B : ℝ) (hA : A ≠ 0) (hAB : A + K * B ≠ 0) (v : Fin K → ℝ) :
    v ⬝ᵥ ((A • (1 : Matrix (Fin K) (Fin K) ℝ) + B • J K)⁻¹ *ᵥ v) =
      (∑ k, v k ^ 2) / A - B / (A * (A + K * B)) * (∑ k, v k) ^ 2 := by
  rw [cs_inv K A B hA hAB]
  simp only [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_add,
    dotProduct_smul, smul_eq_mul]
  have hJ : J K *ᵥ v = fun _ => ∑ k, v k := by
    ext i; simp [J, Matrix.mulVec, dotProduct]
  rw [hJ]
  have e : v ⬝ᵥ (fun _ => ∑ k, v k) = (∑ k, v k) ^ 2 := by
    simp only [dotProduct, ← Finset.sum_mul, sq]
  have e' : v ⬝ᵥ v = ∑ k, v k ^ 2 := by simp [dotProduct, sq]
  rw [e, e']
  ring

end RegAggMatAux

namespace RegAggregation.Posterior
open RegAggMatAux

lemma pk_facts (K : ℕ) (hK : 2 ≤ K) (θ : Fin 3 → ℝ) (hθ : θ ∈ PK K) :
    0 < θ 1 ∧ θ 1 < 1 ∧ 0 ≤ θ 2 ∧ θ 2 < θ 1 ∧ θ 1 ≤ θ 0 ∧
      (K : ℝ) * θ 1 ^ 2 - θ 1 ≤ ((K : ℝ) - 1) * θ 2 := by
  obtain ⟨h1, h2, h3⟩ := hθ
  have hK1 : (1 : ℝ) < K := by exact_mod_cast (show 1 < K by omega)
  have hK1' : (0 : ℝ) < (K : ℝ) - 1 := by linarith
  have h0 : 0 ≤ θ 2 := le_trans (le_max_left _ _) h1
  have hq : ((K : ℝ) * θ 1 ^ 2 - θ 1) / ((K : ℝ) - 1) ≤ θ 2 := le_trans (le_max_right _ _) h1
  have hq' : (K : ℝ) * θ 1 ^ 2 - θ 1 ≤ ((K : ℝ) - 1) * θ 2 := by
    rw [div_le_iff₀ hK1'] at hq; linarith
  have hg : 0 < θ 1 := lt_of_le_of_lt h0 h2
  refine ⟨hg, ?_, h0, h2, h3, hq'⟩
  by_contra hc
  have := mul_pos hK1' (sub_pos.2 h2)
  have hc' : 1 ≤ θ 1 := not_lt.mp hc
  nlinarith [mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ K) hg.le) (sub_nonneg.2 hc')]

lemma Lam_eq (K : ℕ) (θ : Fin 3 → ℝ) :
    Lam K θ = ((θ 0 - θ 2) / (1 - θ 1)) • (1 : Matrix (Fin K) (Fin K) ℝ) +
      (θ 2 / (1 - θ 1)) • J K := by
  rw [Lam, smul_add, smul_smul, smul_smul]
  simp only [div_eq_inv_mul]
  rfl

lemma eta1_eq (K : ℕ) (θ : Fin 3 → ℝ) :
    eta1 K θ = (θ 0 - θ 2) / (1 - θ 1) + K * (θ 2 / (1 - θ 1)) := by
  rw [eta1]; ring

theorem det_Lam' (K : ℕ) (hK : 2 ≤ K) (θ : Fin 3 → ℝ) (hθ : θ ∈ PK K) :
    (Lam K θ).det = eta1 K θ * eta2 θ ^ (K - 1) := by
  obtain ⟨_, hg1, _, hrg, hgd, _⟩ := pk_facts K hK θ hθ
  have hs : 0 < 1 - θ 1 := by linarith
  have hA : (θ 0 - θ 2) / (1 - θ 1) ≠ 0 := (div_pos (by linarith) hs).ne'
  rw [Lam_eq, cs_det K _ _ hA (by omega), eta1_eq, eta2]
  ring

theorem quadratic_form' (K : ℕ) (hK : 2 ≤ K) (μ0 : ℝ) (θ : Fin 3 → ℝ) (hθ : θ ∈ PK K)
    (P : Fin K → ℝ) :
    (fun k => P k - μ0 / Real.sqrt (1 - θ 1)) ⬝ᵥ
        ((Lam K θ)⁻¹ *ᵥ (fun k => P k - μ0 / Real.sqrt (1 - θ 1))) =
      (K : ℝ) * (SP P / eta2 θ + (Pbar P - μ0 / Real.sqrt (1 - θ 1)) ^ 2 / eta1 K θ) := by
  obtain ⟨_, hg1, h20, hrg, hgd, _⟩ := pk_facts K hK θ hθ
  have hs : 0 < 1 - θ 1 := by linarith
  have hApos : 0 < (θ 0 - θ 2) / (1 - θ 1) := div_pos (by linarith) hs
  have hBnn : 0 ≤ θ 2 / (1 - θ 1) := div_nonneg h20 hs.le
  have hKpos : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  have hAB : 0 < (θ 0 - θ 2) / (1 - θ 1) + K * (θ 2 / (1 - θ 1)) := by positivity
  rw [Lam_eq, cs_quad K _ _ hApos.ne' hAB.ne', eta1_eq, ← eta2]
  set A := eta2 θ
  set B := θ 2 / (1 - θ 1)
  set m := μ0 / Real.sqrt (1 - θ 1)
  have hA : A ≠ 0 := hApos.ne'
  have hAB' : A + K * B ≠ 0 := hAB.ne'
  have hK0 : (K : ℝ) ≠ 0 := hKpos.ne'
  simp only [SP, Pbar]
  have e1 : ∑ k, (P k - m) ^ 2 = ∑ k, P k ^ 2 - 2 * m * ∑ k, P k + K * m ^ 2 := by
    simp only [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Finset.mul_sum]
    congr 1; congr 1; apply Finset.sum_congr rfl; intro k _; ring
  have e2 : ∑ k, (P k - m) = ∑ k, P k - K * m := by
    simp [Finset.sum_sub_distrib]
  rw [e1, e2]
  field_simp
  ring

end RegAggregation.Posterior

open RegAggregation.Posterior in
theorem solution (K : ℕ) (hK : 2 ≤ K) (μ0 : ℝ) (θ : Fin 3 → ℝ) (hθ : θ ∈ PK K)
    (P : Fin K → ℝ) :
    (fun k => P k - μ0 / Real.sqrt (1 - θ 1)) ⬝ᵥ
        ((Lam K θ)⁻¹ *ᵥ (fun k => P k - μ0 / Real.sqrt (1 - θ 1))) =
      (K : ℝ) * (SP P / eta2 θ + (Pbar P - μ0 / Real.sqrt (1 - θ 1)) ^ 2 / eta1 K θ) :=
  quadratic_form' K hK μ0 θ hθ P
