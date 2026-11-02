-- Prove2me | solution 1 for StochSQP.Vanishing.eq_14
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T11:49:37.823193+00:00
-- url     : https://prove2.me/submissions/35acf6dd-6b05-4055-b65f-8c9d4f7e67b6

import Mathlib
import Definitions.Def_StochSQP_Vanishing_Model

open scoped InnerProductSpace RealInnerProductSpace
open StochSQP.Vanishing

namespace StochSQPVanT3Aux

lemma bound_of_isBounded {α : Type*} [SeminormedAddCommGroup α] {S : Set α}
    (h : Bornology.IsBounded S) : ∃ C, 0 < C ∧ ∀ y ∈ S, ‖y‖ ≤ C := by
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.1 h
  exact ⟨max C 1, by positivity, fun y hy => (hC y hy).trans (le_max_left _ _)⟩

lemma cauchy_core {n m : ℕ} (J : E n →L[ℝ] E m) (c : E m) (w : E n)
    (hw : ⟪c, J w⟫_ℝ = ‖w‖ ^ 2) (κ a εv s : ℝ) (hJ : ‖J‖ ≤ κ) (ha : 0 ≤ a)
    (haκ : a * κ ^ 2 ≤ 1) (hεv : 0 < εv) (hs : 0 ≤ s)
    (h : εv * (‖c‖ - ‖c + a • J (-w)‖) ≤ s) : εv * a * ‖w‖ ^ 2 ≤ 2 * ‖c‖ * s := by
  have e1 : c + a • J (-w) = c - a • J w := by rw [map_neg, smul_neg, sub_eq_add_neg]
  rw [e1] at h
  set q := ‖c - a • J w‖ with hqdef
  have hJw : ‖J w‖ ≤ κ * ‖w‖ :=
    (J.le_opNorm w).trans (mul_le_mul_of_nonneg_right hJ (norm_nonneg _))
  have hJw2 : ‖J w‖ ^ 2 ≤ κ ^ 2 * ‖w‖ ^ 2 := by
    have := norm_nonneg (J w)
    rw [← mul_pow]; exact pow_le_pow_left₀ this hJw 2
  have hq2 : q ^ 2 = ‖c‖ ^ 2 - 2 * a * ⟪c, J w⟫_ℝ + a ^ 2 * ‖J w‖ ^ 2 := by
    rw [hqdef, norm_sub_sq_real, inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs,
      sq_abs]
    ring
  have hA : a ^ 2 * ‖J w‖ ^ 2 ≤ a * ‖w‖ ^ 2 := by
    have h1 : a ^ 2 * ‖J w‖ ^ 2 ≤ a ^ 2 * (κ ^ 2 * ‖w‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hJw2 (sq_nonneg a)
    have h2 : a ^ 2 * (κ ^ 2 * ‖w‖ ^ 2) = (a * κ ^ 2) * (a * ‖w‖ ^ 2) := by ring
    have h3 : (a * κ ^ 2) * (a * ‖w‖ ^ 2) ≤ 1 * (a * ‖w‖ ^ 2) :=
      mul_le_mul_of_nonneg_right haκ (by positivity)
    linarith
  have hq : q ^ 2 ≤ ‖c‖ ^ 2 - a * ‖w‖ ^ 2 := by rw [hq2, hw]; linarith
  have hq0 : 0 ≤ q := norm_nonneg _
  have hc0 : 0 ≤ ‖c‖ := norm_nonneg _
  have hqc : q ≤ ‖c‖ := by
    have : q ^ 2 ≤ ‖c‖ ^ 2 := by have := mul_nonneg ha (sq_nonneg ‖w‖); linarith
    exact (pow_le_pow_iff_left₀ hq0 hc0 (by norm_num)).1 this
  have k1 : εv * (‖c‖ - q) * (‖c‖ + q) ≤ s * (‖c‖ + q) :=
    mul_le_mul_of_nonneg_right h (by linarith)
  have k2 : s * (‖c‖ + q) ≤ s * (2 * ‖c‖) := mul_le_mul_of_nonneg_left (by linarith) hs
  have k3 : εv * (a * ‖w‖ ^ 2) ≤ εv * (‖c‖ ^ 2 - q ^ 2) :=
    mul_le_mul_of_nonneg_left (by linarith) hεv.le
  nlinarith

lemma inner_c_JJt {n m : ℕ} (P : Problem n m) (x : E n) :
    ⟪P.c x, P.J x (P.Jt x (P.c x))⟫_ℝ = ‖P.Jt x (P.c x)‖ ^ 2 := by
  rw [real_inner_comm, ← real_inner_self_eq_norm_sq]
  simp only [Problem.Jt, ContinuousLinearMap.adjoint_inner_right]

lemma inner_Jt {n m : ℕ} (P : Problem n m) (x : E n) (u : E n) (y : E m) :
    ⟪u, P.Jt x y⟫_ℝ = ⟪P.J x u, y⟫_ℝ := by
  simp only [Problem.Jt, ContinuousLinearMap.adjoint_inner_right]

lemma norm_Jt {n m : ℕ} (P : Problem n m) (x : E n) : ‖P.Jt x‖ = ‖P.J x‖ := by
  simp only [Problem.Jt, LinearIsometryEquiv.norm_map]

end StochSQPVanT3Aux

open StochSQPVanT3Aux

theorem solution {n m : ℕ} (P : Problem n m) (A : Params) (hA : A.Valid)
    (X : Set (E n)) (hA1 : Assumption1 P A.L A.Γ X)
    (R : Run n m) (hR : IsRun P A R) (hX : ∀ k, R.x k ∈ X)
    (κH ζH : ℝ) (hA3 : Assumption3 P R κH ζH) :
    ∀ k : ℕ, R.τ k * ⟪R.u k, R.H k (R.u k)⟫_ℝ +
        A.σ * (‖P.c (R.x k)‖ - ‖P.c (R.x k) + P.J (R.x k) (R.v k)‖) ≤
      deltaL P (R.x k) (R.τ k) (R.g k) (R.d k) := by
  obtain ⟨hL, hΓ, hτ0, hχ0, hζ0, hξ0, hω, hεv, hεv1, hσ, hσ1, hετ, hετ1, hεχ, hεζ, hεζ1,
    hεξ, hεξ1, hη, hη1, hθ⟩ := hA
  have hJd : ∀ k, P.J (R.x k) (R.d k) = P.J (R.x k) (R.v k) := by
    intro k
    obtain ⟨-, -, -, -, -, -, hJu, hdd, -⟩ := hR k
    rw [hdd, map_add, hJu, add_zero]
  have hs0 : ∀ k, 0 ≤ ‖P.c (R.x k)‖ - ‖P.c (R.x k) + P.J (R.x k) (R.v k)‖ := by
    intro k
    obtain ⟨-, -, -, -, hcau, -⟩ := hR k
    have h0 := hcau 0 ⟨le_rfl, hω.le⟩
    simp only [zero_smul, add_zero, sub_self, mul_zero] at h0
    exact h0
  -- τ_k ≥ 0
  have hstep : ∀ k, 0 ≤ prev R.τ A.τ₀ k → 0 ≤ R.τ k := by
    intro k hp
    obtain ⟨-, -, -, -, -, -, -, -, hd0, hd1, -⟩ := hR k
    by_cases hd : R.d k = 0
    · rw [(hd0 hd).1]; exact hp
    obtain ⟨htr, -⟩ := hd1 hd
    by_cases hD : ⟪R.g k, R.d k⟫_ℝ + ⟪R.u k, R.H k (R.u k)⟫_ℝ ≤ 0
    · rw [htr.1 hD]; exact hp
    push_neg at hD
    have h2 := htr.2 hD
    simp only [hJd k] at h2
    by_cases hpt : prev R.τ A.τ₀ k ≤ (1 - A.σ) * (‖P.c (R.x k)‖ -
        ‖P.c (R.x k) + P.J (R.x k) (R.v k)‖) / (⟪R.g k, R.d k⟫_ℝ + ⟪R.u k, R.H k (R.u k)⟫_ℝ)
    · rw [h2.1 hpt]; exact hp
    push_neg at hpt
    rw [h2.2 hpt]
    exact le_min (mul_nonneg (by linarith) hp)
      (div_nonneg (mul_nonneg (by linarith) (hs0 k)) hD.le)
  have hτnn : ∀ k, 0 ≤ R.τ k := by
    intro k
    induction k with
    | zero => exact hstep 0 hτ0.le
    | succ j ih => exact hstep (j + 1) ih
  intro k
  obtain ⟨-, -, hvr, -, -, -, hJu, hdd, hd0, hd1, -⟩ := hR k
  by_cases hd : R.d k = 0
  · -- d_k = 0 forces u_k = v_k = 0
    obtain ⟨y, hy⟩ := LinearMap.mem_range.1 hvr
    have horth : ⟪R.v k, R.u k⟫_ℝ = 0 := by
      have : (P.Jt (R.x k) : E m →ₗ[ℝ] E n) y = P.Jt (R.x k) y := rfl
      rw [← hy, this, real_inner_comm, inner_Jt, hJu, inner_zero_left]
    have hu : R.u k = -R.v k := by
      rw [hdd] at hd; exact eq_neg_of_add_eq_zero_right hd
    rw [hu, inner_neg_right, neg_eq_zero, real_inner_self_eq_norm_sq] at horth
    have hv0 : R.v k = 0 := norm_eq_zero.1 (pow_eq_zero_iff (n := 2) (by norm_num) |>.1 horth)
    rw [hu, hv0, hd]
    simp [deltaL]
  obtain ⟨htr, -⟩ := hd1 hd
  have hΔ : deltaL P (R.x k) (R.τ k) (R.g k) (R.d k) = -R.τ k * ⟪R.g k, R.d k⟫_ℝ +
      (‖P.c (R.x k)‖ - ‖P.c (R.x k) + P.J (R.x k) (R.v k)‖) := by
    simp only [deltaL, hJd k]; ring
  rw [hΔ]
  set s := ‖P.c (R.x k)‖ - ‖P.c (R.x k) + P.J (R.x k) (R.v k)‖ with hsdef
  have hs := hs0 k
  rw [← hsdef] at hs
  set D := ⟪R.g k, R.d k⟫_ℝ + ⟪R.u k, R.H k (R.u k)⟫_ℝ with hDdef
  have hτk := hτnn k
  by_cases hD : D ≤ 0
  · have h1 : R.τ k * D ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hτk hD
    have h2 : A.σ * s ≤ s := by nlinarith
    rw [hDdef] at h1
    nlinarith
  push_neg at hD
  have h2 := htr.2 hD
  simp only [hJd k] at h2
  have hle : R.τ k ≤ (1 - A.σ) * s / D := by
    by_cases hpt : prev R.τ A.τ₀ k ≤ (1 - A.σ) * s / D
    · rw [h2.1 hpt]; exact hpt
    · push_neg at hpt; rw [h2.2 hpt]; exact min_le_right _ _
  have h3 : R.τ k * D ≤ (1 - A.σ) * s := by
    rwa [le_div_iff₀ hD] at hle
  rw [hDdef] at h3
  nlinarith
