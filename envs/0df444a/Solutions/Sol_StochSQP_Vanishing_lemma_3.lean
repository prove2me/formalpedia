-- Prove2me | solution 1 for StochSQP.Vanishing.lemma_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T12:03:06.259768+00:00
-- url     : https://prove2.me/submissions/a99011c8-e94d-47c4-b01e-f1207026ca58

import Mathlib
import Definitions.Def_StochSQP_Vanishing_Model
import Theorems.Thm_StochSQP_Vanishing_lemma_2

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

theorem tau_nonneg_aux {n m : ℕ} (P : Problem n m) (A : Params) (hA : A.Valid)
    (R : Run n m) (hR : IsRun P A R) : ∀ k, 0 ≤ R.τ k := by
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
  exact hτnn

theorem eq14_aux {n m : ℕ} (P : Problem n m) (A : Params) (hA : A.Valid)
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

set_option maxHeartbeats 2000000 in
theorem solution {n m : ℕ} (P : Problem n m) (A : Params) (hA : A.Valid)
    (X : Set (E n)) (hA1 : Assumption1 P A.L A.Γ X)
    (κH ζH : ℝ) :
    ∃ ξmin > (0 : ℝ), ∀ R : Run n m, IsRun P A R → (∀ k, R.x k ∈ X) →
      Assumption3 P R κH ζH →
        ∃ K : ℕ, (∀ k ≥ K, R.ξ k = R.ξ K) ∧ ξmin ≤ R.ξ K := by
  obtain ⟨χmax, hχmax, ζmn, hζmn, hL2⟩ := StochSQP.Vanishing.lemma_2 P A hA X hA1 κH ζH
  have hA' := hA
  obtain ⟨hL, hΓ, hτ0, hχ0, hζ0, hξ0, hω, hεv, hεv1, hσ, hσ1, hετ, hετ1, hεχ, hεζ, hεζ1,
    hεξ, hεξ1, hη, hη1, hθ⟩ := hA'
  have hA1' := hA1
  obtain ⟨-, -, -, -, -, -, -, -, -, hcB, -, hJB⟩ := hA1'
  obtain ⟨κc, hκc, hc⟩ := bound_of_isBounded hcB
  obtain ⟨κJ, hκJ, hJ⟩ := bound_of_isBounded hJB
  set a := min A.ω (1 / κJ ^ 2) with ha
  have ha0 : 0 < a := lt_min hω (by positivity)
  have haω : a ≤ A.ω := min_le_left _ _
  have haJ : a * κJ ^ 2 ≤ 1 := by
    have : a ≤ 1 / κJ ^ 2 := min_le_right _ _
    rw [le_div_iff₀ (by positivity)] at this; linarith
  by_cases hpos : 0 < ζH
  swap
  · refine ⟨1, one_pos, ?_⟩
    intro R _ _ hA3
    exact absurd hA3.2.1 hpos
  set c1 := ζH * A.χ₀ / (A.χ₀ + 1) with hc1
  set c2 := A.σ * (A.εv * a) / (2 * κc * (1 + χmax) * A.ω ^ 2) with hc2
  have hc10 : 0 < c1 := by positivity
  have hc20 : 0 < c2 := by positivity
  set ξlb := min c1 c2 with hξlb
  have hξlb0 : 0 < ξlb := lt_min hc10 hc20
  set ξmin := min A.ξ₀ ((1 - A.εξ) * ξlb) with hξmin
  have hξmin0 : 0 < ξmin := lt_min hξ0 (mul_pos (by linarith) hξlb0)
  refine ⟨ξmin, hξmin0, ?_⟩
  intro R hR hX hA3
  have hτnn := tau_nonneg_aux P A hA R hR
  have h14 := eq14_aux P A hA X hA1 R hR hX κH ζH hA3
  have hA3' := hA3
  obtain ⟨hκH, hζH, hH⟩ := hA3'
  have hcx : ∀ k, ‖P.c (R.x k)‖ ≤ κc := fun k => hc _ ⟨_, hX k, rfl⟩
  have hJx : ∀ k, ‖P.J (R.x k)‖ ≤ κJ := fun k => hJ _ ⟨_, hX k, rfl⟩
  -- χ bounds
  have hχstep : ∀ k, 0 < prev R.χ A.χ₀ k → prev R.χ A.χ₀ k ≤ R.χ k := by
    intro k hp
    obtain ⟨-, -, -, -, -, -, -, -, hd0, hd1, -⟩ := hR k
    by_cases hd : R.d k = 0
    · rw [(hd0 hd).2.1]
    obtain ⟨-, hcz, -, -⟩ := hd1 hd
    by_cases h15 : Cond15 A R k
    · rw [(hcz.1 h15).1]; nlinarith
    · rw [(hcz.2 h15).1]
  have hχlow : ∀ k, A.χ₀ ≤ R.χ k := by
    intro k
    induction k with
    | zero => exact hχstep 0 hχ0
    | succ j ih => exact ih.trans (hχstep (j + 1) (lt_of_lt_of_le hχ0 ih))
  have hχmono : Monotone R.χ := by
    apply monotone_nat_of_le_succ
    intro j
    exact hχstep (j + 1) (lt_of_lt_of_le hχ0 (hχlow j))
  obtain ⟨K2, hK2c, -, hK2max, -⟩ := hL2 R hR hX hA3
  have hχup : ∀ k, R.χ k ≤ χmax := by
    intro k
    rcases le_total k K2 with h | h
    · exact (hχmono h).trans hK2max
    · rw [(hK2c k h).1]; exact hK2max
  -- J d = J v, orthogonality
  have hJd : ∀ k, P.J (R.x k) (R.d k) = P.J (R.x k) (R.v k) := by
    intro k
    obtain ⟨-, -, -, -, -, -, hJu, hdd, -⟩ := hR k
    rw [hdd, map_add, hJu, add_zero]
  have hd2 : ∀ k, ‖R.d k‖ ^ 2 = ‖R.v k‖ ^ 2 + ‖R.u k‖ ^ 2 := by
    intro k
    obtain ⟨-, -, hvr, -, -, -, hJu, hdd, -⟩ := hR k
    obtain ⟨y, hy⟩ := LinearMap.mem_range.1 hvr
    have horth : ⟪R.v k, R.u k⟫_ℝ = 0 := by
      have : (P.Jt (R.x k) : E m →ₗ[ℝ] E n) y = P.Jt (R.x k) y := rfl
      rw [← hy, this, real_inner_comm, inner_Jt, hJu, inner_zero_left]
    rw [hdd, norm_add_sq_real, horth]; ring
  -- Cauchy facts
  have hs : ∀ k, 0 ≤ ‖P.c (R.x k)‖ - ‖P.c (R.x k) + P.J (R.x k) (R.v k)‖ ∧
      A.εv * a * ‖P.Jt (R.x k) (P.c (R.x k))‖ ^ 2 ≤
        2 * ‖P.c (R.x k)‖ * (‖P.c (R.x k)‖ - ‖P.c (R.x k) + P.J (R.x k) (R.v k)‖) := by
    intro k
    obtain ⟨-, -, -, -, hcau, -⟩ := hR k
    have h0 := hcau 0 ⟨le_rfl, hω.le⟩
    simp only [zero_smul, add_zero, sub_self, mul_zero] at h0
    refine ⟨h0, ?_⟩
    exact cauchy_core (P.J (R.x k)) (P.c (R.x k)) _ (inner_c_JJt P (R.x k)) κJ a A.εv _
      (hJx k) ha0.le haJ hεv h0 (hcau a ⟨ha0.le, haω⟩)
  -- τ_k > 0
  have hpos_step : ∀ k, 0 < prev R.τ A.τ₀ k → 0 < R.τ k := by
    intro k hp
    obtain ⟨-, -, -, hvn, -, hlin, hJu, hdd, hd0, hd1, -⟩ := hR k
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
    refine lt_min (mul_pos (by linarith) hp) (div_pos (mul_pos (by linarith) ?_) hD)
    -- s > 0, otherwise v = 0 and the denominator vanishes
    rcases (hs k).1.lt_or_eq with hlt | heq
    · exact hlt
    exfalso
    have hw0 : ‖P.Jt (R.x k) (P.c (R.x k))‖ = 0 := by
      have := (hs k).2
      rw [← heq, mul_zero] at this
      have hpos : 0 < A.εv * a := mul_pos hεv ha0
      have : ‖P.Jt (R.x k) (P.c (R.x k))‖ ^ 2 ≤ 0 := by
        by_contra hh; push_neg at hh; nlinarith
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 (le_antisymm this (sq_nonneg _))
    have hv0 : R.v k = 0 := by
      rw [hw0, mul_zero] at hvn; exact norm_eq_zero.1 (le_antisymm hvn (norm_nonneg _))
    have e : ⟪R.u k, R.H k (R.u k)⟫_ℝ = -⟪R.u k, R.g k⟫_ℝ := by
      have := congrArg (fun z => ⟪R.u k, z⟫_ℝ) hlin
      simp only [inner_add_right, inner_neg_right, inner_Jt, hJu, inner_zero_left, hv0,
        map_zero, inner_zero_right] at this
      linarith
    rw [hdd, hv0, zero_add, e, real_inner_comm] at hD
    linarith
  have hpos : ∀ k, 0 < R.τ k := by
    intro k
    induction k with
    | zero => exact hpos_step 0 hτ0
    | succ j ih => exact hpos_step (j + 1) ih
  -- lower bound on the trial value
  have htrial : ∀ k, R.d k ≠ 0 → ξlb ≤ xiTrial P R k := by
    intro k hd
    obtain ⟨-, -, -, hvn, -, -, hJu, -⟩ := hR k
    obtain ⟨-, -, hHz⟩ := hH k
    have hker : R.u k ∈ LinearMap.ker (P.J (R.x k) : E n →ₗ[ℝ] E m) := by
      simp [LinearMap.mem_ker, hJu]
    have hz := hHz _ hker
    have hΔ := h14 k
    have hs0 := (hs k).1
    have hdpos : 0 < ‖R.d k‖ ^ 2 := by have := norm_pos_iff.2 hd; positivity
    have hχk := hχlow k
    unfold xiTrial
    split_ifs with hT
    · -- tangentially dominated
      have hτk := hpos k
      have hu2 : ‖R.d k‖ ^ 2 * A.χ₀ ≤ ‖R.u k‖ ^ 2 * (A.χ₀ + 1) := by
        rw [hd2 k]
        have : A.χ₀ * ‖R.v k‖ ^ 2 ≤ R.χ k * ‖R.v k‖ ^ 2 :=
          mul_le_mul_of_nonneg_right hχk (sq_nonneg _)
        nlinarith
      have hΔ' : R.τ k * (ζH * ‖R.u k‖ ^ 2) ≤ deltaL P (R.x k) (R.τ k) (R.g k) (R.d k) := by
        have := mul_le_mul_of_nonneg_left hz hτk.le
        have := mul_nonneg hσ.le hs0
        linarith
      refine (min_le_left _ _).trans ?_
      rw [hc1, div_le_div_iff₀ (by positivity) (by positivity)]
      have h1 := mul_le_mul_of_nonneg_left hΔ' (by positivity : (0:ℝ) ≤ A.χ₀ + 1)
      have h2 : ζH * A.χ₀ * (R.τ k * ‖R.d k‖ ^ 2) ≤ R.τ k * ζH * (‖R.u k‖ ^ 2 * (A.χ₀ + 1)) := by
        have := mul_le_mul_of_nonneg_left hu2 (by positivity : (0:ℝ) ≤ R.τ k * ζH)
        nlinarith
      nlinarith
    · -- normally dominated
      push_neg at hT
      have hv2 : ‖R.d k‖ ^ 2 ≤ (1 + χmax) * ‖R.v k‖ ^ 2 := by
        rw [hd2 k]
        have : R.χ k * ‖R.v k‖ ^ 2 ≤ χmax * ‖R.v k‖ ^ 2 :=
          mul_le_mul_of_nonneg_right (hχup k) (sq_nonneg _)
        nlinarith
      set w := ‖P.Jt (R.x k) (P.c (R.x k))‖ with hw
      have hvw : ‖R.v k‖ ^ 2 ≤ A.ω ^ 2 * w ^ 2 := by
        rw [← mul_pow]; exact pow_le_pow_left₀ (norm_nonneg _) hvn 2
      set s := ‖P.c (R.x k)‖ - ‖P.c (R.x k) + P.J (R.x k) (R.v k)‖ with hsd
      have hsw : A.εv * a * w ^ 2 ≤ 2 * κc * s := by
        have h1 := (hs k).2
        have h2 : 2 * ‖P.c (R.x k)‖ * s ≤ 2 * κc * s :=
          mul_le_mul_of_nonneg_right (by linarith [hcx k]) hs0
        linarith
      have hΔ' : A.σ * s ≤ deltaL P (R.x k) (R.τ k) (R.g k) (R.d k) := by
        have := mul_nonneg (hpos k).le (le_trans (by positivity) hz)
        linarith
      refine (min_le_right _ _).trans ?_
      rw [hc2, div_le_div_iff₀ (by positivity) hdpos]
      -- σ εv a ‖d‖² ≤ Δ · 2κc(1+χmax)ω²
      have k1 : A.σ * (A.εv * a) * ‖R.d k‖ ^ 2 ≤
          A.σ * (A.εv * a) * ((1 + χmax) * (A.ω ^ 2 * w ^ 2)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact hv2.trans (mul_le_mul_of_nonneg_left hvw (by positivity))
      have k2 : (1 + χmax) * A.ω ^ 2 * (A.σ * (A.εv * a * w ^ 2)) ≤
          (1 + χmax) * A.ω ^ 2 * (A.σ * (2 * κc * s)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsw hσ.le) (by positivity)
      have k3 : (1 + χmax) * A.ω ^ 2 * (A.σ * (2 * κc * s)) ≤
          (1 + χmax) * A.ω ^ 2 * (2 * κc * deltaL P (R.x k) (R.τ k) (R.g k) (R.d k)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        nlinarith
      linarith
  -- ξ bounds
  have hξstep : ∀ k, ξmin ≤ prev R.ξ A.ξ₀ k → ξmin ≤ R.ξ k ∧ R.ξ k ≤ prev R.ξ A.ξ₀ k := by
    intro k hp
    obtain ⟨-, -, -, -, -, -, -, -, hd0, hd1, -⟩ := hR k
    by_cases hd : R.d k = 0
    · rw [(hd0 hd).2.2.2.1]; exact ⟨hp, le_rfl⟩
    obtain ⟨-, -, hxi, -⟩ := hd1 hd
    have ht := htrial k hd
    by_cases hh : prev R.ξ A.ξ₀ k ≤ xiTrial P R k
    · rw [hxi.1 hh]; exact ⟨hp, le_rfl⟩
    · push_neg at hh; rw [hxi.2 hh]
      have hp0 : 0 < prev R.ξ A.ξ₀ k := lt_of_lt_of_le hξmin0 hp
      refine ⟨le_min ?_ ?_, (min_le_left _ _).trans (by nlinarith)⟩
      · have : (1 - A.εξ) * ξlb ≤ (1 - A.εξ) * prev R.ξ A.ξ₀ k :=
          mul_le_mul_of_nonneg_left (by linarith) (by linarith)
        exact (min_le_right _ _).trans this
      · have : ξmin ≤ ξlb := (min_le_right _ _).trans (by nlinarith)
        linarith
  have hξb : ∀ k, ξmin ≤ R.ξ k ∧ R.ξ k ≤ prev R.ξ A.ξ₀ k := by
    intro k
    induction k with
    | zero => exact hξstep 0 (min_le_left _ _)
    | succ j ih => exact hξstep (j + 1) ih.1
  -- stabilization
  have hbdd : BddBelow (Set.range R.ξ) := ⟨ξmin, by rintro _ ⟨k, rfl⟩; exact (hξb k).1⟩
  set Lξ := ⨅ k, R.ξ k with hLξ
  have hLpos : 0 < Lξ := lt_of_lt_of_le hξmin0 (le_ciInf fun k => (hξb k).1)
  have h1ε : 0 < 1 - A.εξ := by linarith
  obtain ⟨K, hK⟩ := exists_lt_of_ciInf_lt (show Lξ < Lξ / (1 - A.εξ) by
    rw [lt_div_iff₀ h1ε]; nlinarith)
  have hconst : ∀ j, R.ξ (K + j) = R.ξ K := by
    intro j
    induction j with
    | zero => rfl
    | succ j ih =>
      show R.ξ (K + j + 1) = R.ξ K
      obtain ⟨-, -, -, -, -, -, -, -, hd0, hd1, -⟩ := hR (K + j + 1)
      have hprev : prev R.ξ A.ξ₀ (K + j + 1) = R.ξ (K + j) := rfl
      by_cases hd : R.d (K + j + 1) = 0
      · rw [(hd0 hd).2.2.2.1, hprev, ih]
      obtain ⟨-, -, hxi, -⟩ := hd1 hd
      by_cases hh : prev R.ξ A.ξ₀ (K + j + 1) ≤ xiTrial P R (K + j + 1)
      · rw [hxi.1 hh, hprev, ih]
      · exfalso
        push_neg at hh
        have e := hxi.2 hh
        have hle : Lξ ≤ R.ξ (K + j + 1) := ciInf_le hbdd _
        rw [e, hprev, ih] at hle
        have := min_le_left ((1 - A.εξ) * R.ξ K) (xiTrial P R (K + j + 1))
        rw [lt_div_iff₀ h1ε] at hK
        nlinarith
  refine ⟨K, ?_, (hξb K).1⟩
  intro k hk
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
  exact hconst j
