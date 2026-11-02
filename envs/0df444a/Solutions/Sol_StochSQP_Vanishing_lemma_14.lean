-- Prove2me | solution 1 for StochSQP.Vanishing.lemma_14
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T11:53:40.252189+00:00
-- url     : https://prove2.me/submissions/293415c3-fbd1-40cf-9035-94e576843736

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

theorem l7_aux {n m : ℕ} (P : Problem n m) (A : Params) (hA : A.Valid)
    (X : Set (E n)) (hA1 : Assumption1 P A.L A.Γ X)
    (R : Run n m) (hR : IsRun P A R) (hX : ∀ k, R.x k ∈ X)
    (κH ζH : ℝ) (hA3 : Assumption3 P R κH ζH)
    (κg : ℝ) (hκg : 0 < κg) (hg : ∀ k, ‖R.g k - P.grad (R.x k)‖ ≤ κg) :
    ∃ κu > (0 : ℝ), ∀ k : ℕ, ‖R.u k‖ ≤ κu := by
  obtain ⟨hL, hΓ, hτ0, hχ0, hζ0, hξ0, hω, hεv, hεv1, hσ, hσ1, hετ, hετ1, hεχ, hεζ, hεζ1,
    hεξ, hεξ1, hη, hη1, hθ⟩ := hA
  obtain ⟨-, -, -, -, -, -, -, -, hgB, hcB, -, hJB⟩ := hA1
  obtain ⟨κc, hκc, hc⟩ := bound_of_isBounded hcB
  obtain ⟨κJ, hκJ, hJ⟩ := bound_of_isBounded hJB
  obtain ⟨κ0, hκ0, hgr⟩ := bound_of_isBounded hgB
  obtain ⟨hκH, hζH, hH⟩ := hA3
  have hcx : ∀ k, ‖P.c (R.x k)‖ ≤ κc := fun k => hc _ ⟨_, hX k, rfl⟩
  have hJx : ∀ k, ‖P.J (R.x k)‖ ≤ κJ := fun k => hJ _ ⟨_, hX k, rfl⟩
  have hgx : ∀ k, ‖P.grad (R.x k)‖ ≤ κ0 := fun k => hgr _ ⟨_, hX k, rfl⟩
  have hw : ∀ k, ‖P.Jt (R.x k) (P.c (R.x k))‖ ≤ κJ * κc := by
    intro k
    calc ‖P.Jt (R.x k) (P.c (R.x k))‖ ≤ ‖P.Jt (R.x k)‖ * ‖P.c (R.x k)‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ κJ * κc := by
        rw [norm_Jt]; exact mul_le_mul (hJx k) (hcx k) (norm_nonneg _) hκJ.le
  set G := κ0 + κg with hG
  have hG0 : 0 < G := by positivity
  have hgk : ∀ k, ‖R.g k‖ ≤ G := by
    intro k
    have h2 : ‖R.g k‖ ≤ ‖P.grad (R.x k)‖ + ‖R.g k - P.grad (R.x k)‖ := by
      have := norm_add_le (P.grad (R.x k)) (R.g k - P.grad (R.x k))
      simpa using this
    linarith [hgx k, hg k]
  set V := A.ω * (κJ * κc) with hV
  have hV0 : 0 ≤ V := by positivity
  have hvk : ∀ k, ‖R.v k‖ ≤ V := by
    intro k
    obtain ⟨-, -, -, hvn, -⟩ := hR k
    exact hvn.trans (mul_le_mul_of_nonneg_left (hw k) hω.le)
  set U := (G + κH * V) / ζH with hU
  have hU0 : 0 < U := by positivity
  refine ⟨U, hU0, ?_⟩
  intro k
  obtain ⟨-, -, -, -, -, hlin, hJu, -⟩ := hR k
  obtain ⟨-, hHn, hHz⟩ := hH k
  have hker : R.u k ∈ LinearMap.ker (P.J (R.x k) : E n →ₗ[ℝ] E m) := by
    simp [LinearMap.mem_ker, hJu]
  have hz := hHz _ hker
  have e : ⟪R.u k, R.H k (R.u k)⟫_ℝ = -⟪R.u k, R.g k⟫_ℝ - ⟪R.u k, R.H k (R.v k)⟫_ℝ := by
    have := congrArg (fun z => ⟪R.u k, z⟫_ℝ) hlin
    simp only [inner_add_right, inner_neg_right, inner_Jt, hJu, inner_zero_left] at this
    linarith
  have b1 : -⟪R.u k, R.g k⟫_ℝ ≤ ‖R.u k‖ * G := by
    have h1 := abs_real_inner_le_norm (R.u k) (R.g k)
    have h2 := neg_le_abs ⟪R.u k, R.g k⟫_ℝ
    have h3 : ‖R.u k‖ * ‖R.g k‖ ≤ ‖R.u k‖ * G :=
      mul_le_mul_of_nonneg_left (hgk k) (norm_nonneg _)
    linarith
  have b2 : -⟪R.u k, R.H k (R.v k)⟫_ℝ ≤ ‖R.u k‖ * (κH * V) := by
    have h1 := abs_real_inner_le_norm (R.u k) (R.H k (R.v k))
    have h2 := neg_le_abs ⟪R.u k, R.H k (R.v k)⟫_ℝ
    have h3 : ‖R.H k (R.v k)‖ ≤ κH * V :=
      ((R.H k).le_opNorm _).trans (mul_le_mul hHn (hvk k) (norm_nonneg _) hκH.le)
    have h4 : ‖R.u k‖ * ‖R.H k (R.v k)‖ ≤ ‖R.u k‖ * (κH * V) :=
      mul_le_mul_of_nonneg_left h3 (norm_nonneg _)
    linarith
  have hq7 : ζH * ‖R.u k‖ ^ 2 ≤ ‖R.u k‖ * (G + κH * V) := by
    rw [mul_add]; linarith
  rw [hU, le_div_iff₀ hζH]
  by_cases hu0 : ‖R.u k‖ = 0
  · rw [hu0, zero_mul]; positivity
  · have hpos : 0 < ‖R.u k‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hu0)
    have h5 : ‖R.u k‖ * (‖R.u k‖ * ζH) ≤ ‖R.u k‖ * (G + κH * V) := by
      have : ‖R.u k‖ * (‖R.u k‖ * ζH) = ζH * ‖R.u k‖ ^ 2 := by ring
      rw [this]; exact hq7
    exact le_of_mul_le_mul_left h5 hpos

set_option maxHeartbeats 1000000 in
theorem solution {n m : ℕ} (P : Problem n m) (A : Params) (hA : A.Valid)
    (X : Set (E n)) (hA1 : Assumption1 P A.L A.Γ X)
    (R : Run n m) (hR : IsRun P A R) (hX : ∀ k, R.x k ∈ X)
    (κH ζH : ℝ) (hA3 : Assumption3 P R κH ζH)
    (M : ℝ) (hM : 0 < M) (hg : ∀ k, ‖R.g k - P.grad (R.x k)‖ ^ 2 ≤ M)
    (hτ : Filter.Tendsto R.τ Filter.atTop (nhds 0)) :
    ∃ κβ > (0 : ℝ), ∀ k : ℕ,
      (¬ R.TangDom k →
        R.α k * R.τ k * ⟪P.grad (R.x k) - R.g k, R.d k⟫_ℝ ≤ R.β k * R.τ k * κβ) ∧
      (R.TangDom k →
        R.α k * R.τ k * ⟪P.grad (R.x k) - R.g k, R.d k⟫_ℝ ≤
          R.β k * R.τ k * max (R.β k) (R.τ k) * κβ) := by
  have hτnn := tau_nonneg_aux P A hA R hR
  have h14 := eq14_aux P A hA X hA1 R hR hX κH ζH hA3
  have hA' := hA
  obtain ⟨hL, hΓ, hτ0, hχ0, hζ0, hξ0, hω, hεv, hεv1, hσ, hσ1, hετ, hετ1, hεχ, hεζ, hεζ1,
    hεξ, hεξ1, hη, hη1, hθ⟩ := hA'
  have hA1' := hA1
  obtain ⟨-, -, -, -, -, -, -, -, -, hcB, -, hJB⟩ := hA1'
  obtain ⟨κc, hκc, hc⟩ := bound_of_isBounded hcB
  obtain ⟨κJ, hκJ, hJ⟩ := bound_of_isBounded hJB
  have hA3' := hA3
  obtain ⟨hκH, hζH, hH⟩ := hA3'
  -- gradient error bound
  set Eg := max M 1 with hEg
  have hEg0 : 0 < Eg := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hgk : ∀ k, ‖R.g k - P.grad (R.x k)‖ ≤ Eg := by
    intro k
    by_cases h : ‖R.g k - P.grad (R.x k)‖ ≤ 1
    · exact h.trans (le_max_right _ _)
    · push_neg at h
      have := hg k
      have : ‖R.g k - P.grad (R.x k)‖ ≤ M := by nlinarith
      exact this.trans (le_max_left _ _)
  obtain ⟨κu, hκu, hu⟩ := l7_aux P A hA X hA1 R hR hX κH ζH hA3 Eg hEg0 hgk
  -- bound on ‖d_k‖
  set V := A.ω * (κJ * κc) with hV
  have hV0 : 0 ≤ V := by positivity
  have hvk : ∀ k, ‖R.v k‖ ≤ V := by
    intro k
    obtain ⟨-, -, -, hvn, -⟩ := hR k
    have hcx : ‖P.c (R.x k)‖ ≤ κc := hc _ ⟨_, hX k, rfl⟩
    have hJx : ‖P.J (R.x k)‖ ≤ κJ := hJ _ ⟨_, hX k, rfl⟩
    have hw : ‖P.Jt (R.x k) (P.c (R.x k))‖ ≤ κJ * κc := by
      calc ‖P.Jt (R.x k) (P.c (R.x k))‖ ≤ ‖P.Jt (R.x k)‖ * ‖P.c (R.x k)‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ ≤ κJ * κc := by
          rw [norm_Jt]; exact mul_le_mul hJx hcx (norm_nonneg _) hκJ.le
    exact hvn.trans (mul_le_mul_of_nonneg_left hw hω.le)
  have hdk : ∀ k, ‖R.d k‖ ≤ V + κu := by
    intro k
    obtain ⟨-, -, -, -, -, -, -, hdd, -⟩ := hR k
    rw [hdd]; exact (norm_add_le _ _).trans (add_le_add (hvk k) (hu k))
  -- Δl ≥ 0
  have hΔ : ∀ k, 0 ≤ deltaL P (R.x k) (R.τ k) (R.g k) (R.d k) := by
    intro k
    obtain ⟨-, -, -, -, hcau, -, hJu, -⟩ := hR k
    obtain ⟨-, -, hHz⟩ := hH k
    have hker : R.u k ∈ LinearMap.ker (P.J (R.x k) : E n →ₗ[ℝ] E m) := by
      simp [LinearMap.mem_ker, hJu]
    have hz := hHz _ hker
    have h0 := hcau 0 ⟨le_rfl, hω.le⟩
    simp only [zero_smul, add_zero, sub_self, mul_zero] at h0
    have := h14 k
    have h1 : 0 ≤ R.τ k * ⟪R.u k, R.H k (R.u k)⟫_ℝ :=
      mul_nonneg (hτnn k) (le_trans (by positivity) hz)
    have h2 : 0 ≤ A.σ * (‖P.c (R.x k)‖ - ‖P.c (R.x k) + P.J (R.x k) (R.v k)‖) :=
      mul_nonneg hσ.le h0
    linarith
  -- ξ_k ∈ [0, ξ₀]
  have hξstep : ∀ k, 0 ≤ prev R.ξ A.ξ₀ k ∧ prev R.ξ A.ξ₀ k ≤ A.ξ₀ →
      0 ≤ R.ξ k ∧ R.ξ k ≤ A.ξ₀ := by
    intro k ⟨hp0, hp1⟩
    obtain ⟨-, -, -, -, -, -, -, -, hd0, hd1, -⟩ := hR k
    by_cases hd : R.d k = 0
    · rw [(hd0 hd).2.2.2.1]; exact ⟨hp0, hp1⟩
    obtain ⟨-, -, hxi, -⟩ := hd1 hd
    have htr0 : 0 ≤ xiTrial P R k := by
      unfold xiTrial
      split_ifs
      · exact div_nonneg (hΔ k) (mul_nonneg (hτnn k) (sq_nonneg _))
      · exact div_nonneg (hΔ k) (sq_nonneg _)
    by_cases hh : prev R.ξ A.ξ₀ k ≤ xiTrial P R k
    · rw [hxi.1 hh]; exact ⟨hp0, hp1⟩
    · push_neg at hh; rw [hxi.2 hh]
      refine ⟨le_min (mul_nonneg (by linarith) hp0) htr0, ?_⟩
      exact (min_le_left _ _).trans (by nlinarith)
  have hξ : ∀ k, 0 ≤ R.ξ k ∧ R.ξ k ≤ A.ξ₀ := by
    intro k
    induction k with
    | zero => exact hξstep 0 ⟨hξ0.le, le_rfl⟩
    | succ j ih => exact hξstep (j + 1) ih
  -- constants
  set C1 := 2 * (1 - A.η) * A.ξ₀ / A.Γ + A.θ with hC1
  have hη' : 0 < 1 - A.η := by linarith
  have hC1pos : 0 < C1 := by positivity
  set E0 := Eg * (V + κu) with hE0
  have hE00 : 0 < E0 := by positivity
  refine ⟨C1 * E0, by positivity, ?_⟩
  intro k
  obtain ⟨⟨hβ0, hβ1⟩, -, -, -, -, -, -, -, hd0, hd1, -⟩ := hR k
  have hτk := hτnn k
  have hQ : A.Γ ≤ R.τ k * A.L + A.Γ := by have := mul_nonneg hτk hL.le; linarith
  have hQ0 : 0 < R.τ k * A.L + A.Γ := by linarith
  -- bound on α and its sign
  have hαb : 0 ≤ R.α k ∧ R.α k ≤ projHi A R k ∨ (R.d k = 0 ∧ R.α k = 1) := by
    by_cases hd : R.d k = 0
    · exact Or.inr ⟨hd, (hd0 hd).2.2.2.2⟩
    left
    obtain ⟨-, -, -, hal⟩ := hd1 hd
    have hlo0 : 0 ≤ projLo A R k := by
      unfold projLo
      have := (hξ k).1
      split_ifs <;> positivity
    have hhi : projLo A R k ≤ projHi A R k := by
      unfold projHi; have := mul_nonneg hθ (sq_nonneg (R.β k)); linarith
    rw [hal]; unfold proj
    exact ⟨le_trans hlo0 (le_max_left _ _), max_le hhi (min_le_right _ _)⟩
  have hinner : ⟪P.grad (R.x k) - R.g k, R.d k⟫_ℝ ≤ E0 := by
    have := real_inner_le_norm (P.grad (R.x k) - R.g k) (R.d k)
    rw [norm_sub_rev] at this
    exact this.trans (mul_le_mul (hgk k) (hdk k) (norm_nonneg _) hEg0.le)
  -- generic: if α ≤ Bα then LHS ≤ τ Bα E0
  have key : ∀ Bα : ℝ, 0 ≤ Bα → (R.d k ≠ 0 → R.α k ≤ Bα) → (R.d k = 0 → 0 ≤ Bα) →
      R.α k * R.τ k * ⟪P.grad (R.x k) - R.g k, R.d k⟫_ℝ ≤ Bα * R.τ k * E0 := by
    intro Bα hB0 hB hBd
    rcases hαb with ⟨hα0, -⟩ | ⟨hd, -⟩
    · by_cases hin : ⟪P.grad (R.x k) - R.g k, R.d k⟫_ℝ ≤ 0
      · have : R.α k * R.τ k * ⟪P.grad (R.x k) - R.g k, R.d k⟫_ℝ ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hα0 hτk) hin
        have : 0 ≤ Bα * R.τ k * E0 := by positivity
        linarith
      · push_neg at hin
        have hd : R.d k ≠ 0 := by
          intro h; rw [h, inner_zero_right] at hin; exact lt_irrefl _ hin
        have h1 : R.α k * R.τ k ≤ Bα * R.τ k := mul_le_mul_of_nonneg_right (hB hd) hτk
        calc R.α k * R.τ k * ⟪P.grad (R.x k) - R.g k, R.d k⟫_ℝ
            ≤ Bα * R.τ k * ⟪P.grad (R.x k) - R.g k, R.d k⟫_ℝ :=
              mul_le_mul_of_nonneg_right h1 hin.le
          _ ≤ Bα * R.τ k * E0 := mul_le_mul_of_nonneg_left hinner (by positivity)
    · rw [hd, inner_zero_right, mul_zero]; have := hBd hd; positivity
  have hξk := hξ k
  have hlo_le : 2 * (1 - A.η) * R.β k * R.ξ k / (R.τ k * A.L + A.Γ) ≤
      2 * (1 - A.η) * A.ξ₀ / A.Γ * R.β k := by
    rw [div_le_iff₀ hQ0]
    have h1 : 2 * (1 - A.η) * R.β k * R.ξ k ≤ 2 * (1 - A.η) * R.β k * A.ξ₀ :=
      mul_le_mul_of_nonneg_left hξk.2 (by positivity)
    have h2 : 2 * (1 - A.η) * A.ξ₀ / A.Γ * R.β k * A.Γ = 2 * (1 - A.η) * R.β k * A.ξ₀ := by
      field_simp
    have h3 : 2 * (1 - A.η) * A.ξ₀ / A.Γ * R.β k * A.Γ ≤
        2 * (1 - A.η) * A.ξ₀ / A.Γ * R.β k * (R.τ k * A.L + A.Γ) :=
      mul_le_mul_of_nonneg_left hQ (by positivity)
    linarith
  have hβ2 : R.β k ^ 2 ≤ R.β k := by nlinarith
  constructor
  · intro hT
    have hB0 : 0 ≤ C1 * R.β k := by positivity
    have := key (C1 * R.β k) hB0 (by
      intro hd
      rcases hαb with ⟨-, hhi⟩ | ⟨hd', -⟩
      · refine hhi.trans ?_
        unfold projHi projLo
        rw [if_neg (show ¬ (R.χ k * ‖R.v k‖ ^ 2 ≤ ‖R.u k‖ ^ 2) from hT)]
        have : A.θ * R.β k ^ 2 ≤ A.θ * R.β k := mul_le_mul_of_nonneg_left hβ2 hθ
        rw [hC1]; nlinarith
      · exact absurd hd' hd) (fun _ => hB0)
    calc _ ≤ C1 * R.β k * R.τ k * E0 := this
      _ = R.β k * R.τ k * (C1 * E0) := by ring
  · intro hT
    have hmx : 0 ≤ max (R.β k) (R.τ k) := le_trans hβ0.le (le_max_left _ _)
    have hB0 : 0 ≤ C1 * R.β k * max (R.β k) (R.τ k) := by positivity
    have := key (C1 * R.β k * max (R.β k) (R.τ k)) hB0 (by
      intro hd
      rcases hαb with ⟨-, hhi⟩ | ⟨hd', -⟩
      · refine hhi.trans ?_
        unfold projHi projLo
        rw [if_pos (show R.χ k * ‖R.v k‖ ^ 2 ≤ ‖R.u k‖ ^ 2 from hT)]
        have e1 : 2 * (1 - A.η) * R.β k * R.ξ k * R.τ k / (R.τ k * A.L + A.Γ) =
            2 * (1 - A.η) * R.β k * R.ξ k / (R.τ k * A.L + A.Γ) * R.τ k := by ring
        rw [e1]
        have h1 : 2 * (1 - A.η) * R.β k * R.ξ k / (R.τ k * A.L + A.Γ) * R.τ k ≤
            2 * (1 - A.η) * A.ξ₀ / A.Γ * R.β k * R.τ k :=
          mul_le_mul_of_nonneg_right hlo_le hτk
        have h2 : R.β k * R.τ k ≤ R.β k * max (R.β k) (R.τ k) :=
          mul_le_mul_of_nonneg_left (le_max_right _ _) hβ0.le
        have h3 : A.θ * R.β k ^ 2 ≤ A.θ * (R.β k * max (R.β k) (R.τ k)) := by
          apply mul_le_mul_of_nonneg_left _ hθ
          rw [sq]; exact mul_le_mul_of_nonneg_left (le_max_left _ _) hβ0.le
        have h4 : 2 * (1 - A.η) * A.ξ₀ / A.Γ * (R.β k * R.τ k) ≤
            2 * (1 - A.η) * A.ξ₀ / A.Γ * (R.β k * max (R.β k) (R.τ k)) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
        rw [hC1]; nlinarith
      · exact absurd hd' hd) (fun _ => hB0)
    calc _ ≤ C1 * R.β k * max (R.β k) (R.τ k) * R.τ k * E0 := this
      _ = R.β k * R.τ k * max (R.β k) (R.τ k) * (C1 * E0) := by ring
