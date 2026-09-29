-- Prove2me | solution 1 for RobustLS.Tikhonov.dual_optimal_point
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T03:25:41.268237+00:00
-- url     : https://prove2.me/submissions/0d647632-9b1f-46ed-a81a-65ca998efbbb

import Mathlib
import Definitions.Def_RobustLS_Tikhonov_Core

namespace RobustLS.Tikhonov

open Matrix

lemma aux_dop_cs {ι : Type*} [Fintype ι] (p q : ι → ℝ) (hq : eucNorm q ≤ 1) :
    -(p ⬝ᵥ q) ≤ eucNorm p := by
  have h := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun i => -p i) q
  have hp0 : 0 ≤ eucNorm p := Real.sqrt_nonneg _
  have e1 : ∑ i, (fun i => -p i) i * q i = -(p ⬝ᵥ q) := by
    simp [dotProduct, Finset.sum_neg_distrib]
  have e2 : Real.sqrt (∑ i, (fun i => -p i) i ^ 2) = eucNorm p := by
    simp [eucNorm]
  rw [e1, e2] at h
  have h3 : eucNorm p * Real.sqrt (∑ i, q i ^ 2) ≤ eucNorm p := by
    have : Real.sqrt (∑ i, q i ^ 2) = eucNorm q := rfl
    rw [this]
    nlinarith
  linarith

lemma aux_dop_eq {ι : Type*} [Fintype ι] (p q : ι → ℝ) (hq : eucNorm q ≤ 1)
    (hp : 0 < eucNorm p) (hpq : eucNorm p ≤ -(p ⬝ᵥ q)) :
    q = (-(1 / eucNorm p)) • p := by
  set N := eucNorm p with hN
  have hN2 : N ^ 2 = ∑ i, p i ^ 2 := by
    rw [hN, eucNorm, Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg (p i)))]
  have hM2 : ∑ i, q i ^ 2 ≤ 1 := by
    have h0 : 0 ≤ eucNorm q := Real.sqrt_nonneg _
    have : eucNorm q ^ 2 = ∑ i, q i ^ 2 := by
      rw [eucNorm, Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg (q i)))]
    nlinarith
  have hsum : ∑ i, (q i + p i / N) ^ 2 = ∑ i, q i ^ 2 + 2 / N * (p ⬝ᵥ q)
      + (∑ i, p i ^ 2) / N ^ 2 := by
    simp only [dotProduct, Finset.mul_sum, Finset.sum_div, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    field_simp
    ring
  have hle : ∑ i, (q i + p i / N) ^ 2 ≤ 0 := by
    rw [hsum, ← hN2, div_self (pow_ne_zero 2 hp.ne')]
    have : 2 / N * (p ⬝ᵥ q) ≤ -2 := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hp]
      linarith
    linarith
  have hzero : ∀ i ∈ Finset.univ, (q i + p i / N) ^ 2 = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg _)).1
      (le_antisymm hle (Finset.sum_nonneg (fun i _ => sq_nonneg _)))
  funext i
  have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 (hzero i (Finset.mem_univ i))
  simp only [Pi.smul_apply, smul_eq_mul]
  have : q i = -(p i / N) := by linarith
  rw [this]
  ring

end RobustLS.Tikhonov

open RobustLS.Tikhonov
open Matrix

theorem solution {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (b : Fin n → ℝ)
    (x : Fin m → ℝ) (lam tau : ℝ) (z : Fin n → ℝ) (u : Fin m → ℝ) (v : ℝ)
    (hopt : IsSOCPOptimal A b x lam tau) (hlt : tau < lam) (hfeas : IsDualFeasible A z u v)
    (hval : b ⬝ᵥ z - v = lam) :
    z = (-(1 / eucNorm (A *ᵥ x - b))) • (A *ᵥ x - b) ∧
      stackScalar u v = (-(1 / Real.sqrt (eucNorm x ^ 2 + 1))) • stackOne x := by
  obtain ⟨⟨h1, h2⟩, _⟩ := hopt
  obtain ⟨hAu, hz, hw⟩ := hfeas
  set r := A *ᵥ x - b with hr
  set s := stackOne x with hs
  set w := stackScalar u v with hw'
  -- key identity
  have hu : u = -(Aᵀ *ᵥ z) := by
    rw [eq_neg_iff_add_eq_zero, add_comm]; exact hAu
  have hrz : r ⬝ᵥ z = -(x ⬝ᵥ u) - b ⬝ᵥ z := by
    rw [hr, sub_dotProduct, hu, dotProduct_neg, dotProduct_comm (A *ᵥ x) z,
      dotProduct_mulVec, mulVec_transpose, dotProduct_comm x (z ᵥ* A)]
    ring
  have hsw : s ⬝ᵥ w = x ⬝ᵥ u + v := by
    simp [hs, hw', stackOne, stackScalar, dotProduct, Fintype.sum_sum_type]
  have key : lam = -(r ⬝ᵥ z) - (s ⬝ᵥ w) := by
    rw [hrz, hsw, ← hval]; ring
  have cs1 := aux_dop_cs r z hz
  have cs2 := aux_dop_cs s w hw
  have hsnorm : eucNorm s = Real.sqrt (eucNorm x ^ 2 + 1) := by
    have : eucNorm x ^ 2 = ∑ i, x i ^ 2 := by
      rw [eucNorm, Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg (x i)))]
    rw [this]
    simp [hs, eucNorm, stackOne, Fintype.sum_sum_type]
  have hspos : 0 < eucNorm s := by
    rw [hsnorm]; apply Real.sqrt_pos.2; positivity
  have hrpos : 0 < eucNorm r := by linarith
  refine ⟨aux_dop_eq r z hz hrpos (by linarith), ?_⟩
  rw [← hsnorm]
  exact aux_dop_eq s w hw hspos (by linarith)
