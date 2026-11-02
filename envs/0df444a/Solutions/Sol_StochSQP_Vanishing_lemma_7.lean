-- Prove2me | solution 1 for StochSQP.Vanishing.lemma_7
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T11:48:48.504488+00:00
-- url     : https://prove2.me/submissions/4881c8ce-0894-4841-bcbc-fa0571b3d3bd

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
