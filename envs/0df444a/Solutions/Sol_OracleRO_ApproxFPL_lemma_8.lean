-- Prove2me | solution 1 for OracleRO.ApproxFPL.lemma_8
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T13:35:36.655435+00:00
-- url     : https://prove2.me/submissions/6497d3a0-b1f4-4251-8dce-bd3963ac8caf

import Mathlib
import Definitions.Def_OracleRO_ApproxFPL_IsApproxLinOracle
import Definitions.Def_OracleRO_ApproxFPL_FPL

open MeasureTheory ProbabilityTheory

open OracleRO.ApproxFPL in
theorem lemma8_btl {n : ℕ} (K : Set (Fin n → ℝ)) (ε : ℝ)
    (M : (Fin n → ℝ) → (Fin n → ℝ)) (hM : IsApproxLinOracle K ε M)
    (f : ℕ → Fin n → ℝ) (p : Fin n → ℝ) (T : ℕ) :
    M (prefixSum f T + p) ⬝ᵥ (prefixSum f T + p) - ε * T ≤
      ∑ t ∈ Finset.Icc 1 T, M (prefixSum f t + p) ⬝ᵥ f t + M p ⬝ᵥ p := by
  induction T with
  | zero => simp [prefixSum]
  | succ T ih =>
    have hS : prefixSum f (T + 1) = prefixSum f T + f (T + 1) := by
      unfold prefixSum
      rw [Finset.sum_Icc_succ_top (by omega)]
    rw [Finset.sum_Icc_succ_top (by omega)]
    have h1 := (hM (prefixSum f T + p)).2 (M (prefixSum f (T + 1) + p)) (hM _).1
    have e : prefixSum f (T + 1) + p = (prefixSum f T + p) + f (T + 1) := by
      rw [hS]; abel
    rw [e] at h1 ⊢
    rw [dotProduct_add]
    rw [dotProduct_comm (M (prefixSum f T + p)) (prefixSum f T + p)] at ih
    rw [dotProduct_comm (M (prefixSum f T + p + f (T + 1))) (prefixSum f T + p)]
    push_cast
    linarith

theorem lemma8_pert {n : ℕ} (D η : ℝ) (hη : 0 < η) (p x y : Fin n → ℝ)
    (hp : p ∈ Set.Icc (0 : Fin n → ℝ) (fun _ => η⁻¹))
    (hD : ∑ i, |y i - x i| ≤ D) :
    p ⬝ᵥ y - p ⬝ᵥ x ≤ D / η := by
  rw [← dotProduct_sub]
  simp only [dotProduct, Pi.sub_apply]
  have h : ∀ i, p i * (y i - x i) ≤ η⁻¹ * |y i - x i| := by
    intro i
    have h0 : 0 ≤ p i := hp.1 i
    have h1 : p i ≤ η⁻¹ := hp.2 i
    calc p i * (y i - x i) ≤ p i * |y i - x i| :=
          mul_le_mul_of_nonneg_left (le_abs_self _) h0
      _ ≤ η⁻¹ * |y i - x i| := mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
  calc ∑ i, p i * (y i - x i) ≤ ∑ i, η⁻¹ * |y i - x i| := Finset.sum_le_sum (fun i _ => h i)
    _ = η⁻¹ * ∑ i, |y i - x i| := by rw [Finset.mul_sum]
    _ ≤ η⁻¹ * D := mul_le_mul_of_nonneg_left hD (inv_nonneg.mpr hη.le)
    _ = D / η := by rw [div_eq_mul_inv, mul_comm]

open OracleRO.ApproxFPL in
theorem solution {n : ℕ} (K : Set (Fin n → ℝ)) (ε : ℝ) (hε : 0 < ε)
    (M : (Fin n → ℝ) → (Fin n → ℝ)) (hM : IsApproxLinOracle K ε M)
    (D : ℝ) (hD : ∀ x ∈ K, ∀ y ∈ K, ∑ i, |x i - y i| ≤ D)
    (η : ℝ) (hη : 0 < η) (f : ℕ → Fin n → ℝ) (T : ℕ) (hT : 2 ≤ T)
    (p : Fin n → ℝ) (hp : p ∈ Set.Icc (0 : Fin n → ℝ) (fun _ => η⁻¹)) :
    ∀ x ∈ K, prefixSum f T ⬝ᵥ x - D / η - 2 * ε * T ≤
      ∑ t ∈ Finset.Icc 1 T, M (prefixSum f t + p) ⬝ᵥ f t := by
  intro x hx
  have hA := lemma8_btl K ε M hM f p T
  have hB := (hM (prefixSum f T + p)).2 x hx
  have hC := (hM p).2 x hx
  have hP := lemma8_pert D η hη p x (M p) hp (hD (M p) (hM p).1 x hx)
  rw [dotProduct_comm (M (prefixSum f T + p)) (prefixSum f T + p)] at hA
  rw [add_dotProduct] at hB
  rw [dotProduct_comm (M p) p] at hA
  have hT' : (1 : ℝ) ≤ (T : ℝ) := by exact_mod_cast (by omega : 1 ≤ T)
  nlinarith
