-- Prove2me | solution 1 for StochSQP.Vanishing.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T11:48:47.860653+00:00
-- url     : https://prove2.me/submissions/6234f52d-10ba-40ea-990f-f995132c472f

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
    (X : Set (E n)) (hA1 : Assumption1 P A.L A.Γ X) :
    ∃ κv > (0 : ℝ), ∃ ωLow > (0 : ℝ), ∀ R : Run n m, IsRun P A R → (∀ k, R.x k ∈ X) →
      ∀ k : ℕ, 0 < ‖P.c (R.x k)‖ →
        κv * ‖P.Jt (R.x k) (P.c (R.x k))‖ ^ 2 ≤
            ‖P.c (R.x k)‖ * (‖P.c (R.x k)‖ - ‖P.c (R.x k) + P.J (R.x k) (R.v k)‖) ∧
          ωLow * ‖P.Jt (R.x k) (P.c (R.x k))‖ ^ 2 ≤ ‖R.v k‖ ∧
          ‖R.v k‖ ≤ A.ω * ‖P.Jt (R.x k) (P.c (R.x k))‖ := by
  obtain ⟨hL, hΓ, hτ0, hχ0, hζ0, hξ0, hω, hεv, hεv1, hσ, hσ1, hετ, hετ1, hεχ, hεζ, hεζ1,
    hεξ, hεξ1, hη, hη1, hθ⟩ := hA
  obtain ⟨-, -, -, -, -, -, -, -, -, hcB, -, hJB⟩ := hA1
  obtain ⟨κc, hκc, hc⟩ := bound_of_isBounded hcB
  obtain ⟨κJ, hκJ, hJ⟩ := bound_of_isBounded hJB
  set a := min A.ω (1 / κJ ^ 2) with ha
  have ha0 : 0 < a := lt_min hω (by positivity)
  have haω : a ≤ A.ω := min_le_left _ _
  have haJ : a * κJ ^ 2 ≤ 1 := by
    have : a ≤ 1 / κJ ^ 2 := min_le_right _ _
    rw [le_div_iff₀ (by positivity)] at this; linarith
  set κv := A.εv * a / 2 with hκv
  have hκv0 : 0 < κv := by positivity
  refine ⟨κv, hκv0, κv / (κc * κJ), by positivity, ?_⟩
  intro R hR hX k hck
  have hcx : ‖P.c (R.x k)‖ ≤ κc := hc _ ⟨_, hX k, rfl⟩
  have hJx : ‖P.J (R.x k)‖ ≤ κJ := hJ _ ⟨_, hX k, rfl⟩
  obtain ⟨-, -, -, hvn, hcau, -⟩ := hR k
  have h0 := hcau 0 ⟨le_rfl, hω.le⟩
  simp only [zero_smul, add_zero, sub_self, mul_zero] at h0
  have h1 := cauchy_core (P.J (R.x k)) (P.c (R.x k)) _ (inner_c_JJt P (R.x k)) κJ a A.εv _
      hJx ha0.le haJ hεv h0 (hcau a ⟨ha0.le, haω⟩)
  set s := ‖P.c (R.x k)‖ - ‖P.c (R.x k) + P.J (R.x k) (R.v k)‖ with hs
  have first : κv * ‖P.Jt (R.x k) (P.c (R.x k))‖ ^ 2 ≤ ‖P.c (R.x k)‖ * s := by
    rw [hκv]; linarith
  refine ⟨first, ?_, hvn⟩
  have hsJ : s ≤ κJ * ‖R.v k‖ := by
    have t1 : ‖P.c (R.x k)‖ ≤ ‖P.c (R.x k) + P.J (R.x k) (R.v k)‖ + ‖P.J (R.x k) (R.v k)‖ := by
      have := norm_sub_le (P.c (R.x k) + P.J (R.x k) (R.v k)) (P.J (R.x k) (R.v k))
      simpa using this
    have t2 : ‖P.J (R.x k) (R.v k)‖ ≤ κJ * ‖R.v k‖ :=
      (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right hJx (norm_nonneg _))
    rw [hs]; linarith
  have h3 : ‖P.c (R.x k)‖ * s ≤ κc * (κJ * ‖R.v k‖) :=
    mul_le_mul hcx hsJ h0 hκc.le
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  nlinarith
