-- Prove2me | solution 1 for StochSQP.Vanishing.theorem_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T11:43:42.362943+00:00
-- url     : https://prove2.me/submissions/9d3c34a6-3de2-43ac-94dc-a799c2dd2873

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

set_option maxHeartbeats 1000000 in
theorem solution {n m : ℕ} (P : Problem n m) (A : Params) (hA : A.Valid)
    (X : Set (E n)) (hA1 : Assumption1 P A.L A.Γ X)
    (R : Run n m) (hR : IsRun P A R) (hX : ∀ k, R.x k ∈ X)
    (κH ζH : ℝ) (hA3 : Assumption3 P R κH ζH)
    (M : ℝ) (hM : 0 < M) (hg : ∀ k, ‖R.g k - P.grad (R.x k)‖ ^ 2 ≤ M)
    (hτ : Filter.Tendsto R.τ Filter.atTop (nhds 0))
    (h28 : Cond28 A R)
    (hab : (∃ β : ℝ, 0 < β ∧ β < 1 ∧ ∀ k, R.β k = β) ∨
      (¬ Summable R.β ∧ Summable (fun k => R.β k ^ 2) ∧
        ({k : ℕ | ‖R.u k‖ ^ 2 < R.χ k * ‖R.v k‖ ^ 2}.Infinite ∨
          ¬ Summable (fun k => R.β k * R.τ k)))) :
    ∀ γ > (0 : ℝ), ∃ᶠ k in Filter.atTop, ‖P.Jt (R.x k) (P.c (R.x k))‖ < γ := by
  obtain ⟨hL, hΓ, hτ0, hχ0, hζ0, hξ0, hω, hεv, hεv1, hσ, hσ1, hετ, hετ1, hεχ, hεζ, hεζ1,
    hεξ, hεξ1, hη, hη1, hθ⟩ := hA
  obtain ⟨-, -, -, -, -, -, -, -, hgB, hcB, -, hJB⟩ := hA1
  obtain ⟨κc, hκc, hc⟩ := bound_of_isBounded hcB
  obtain ⟨κJ, hκJ, hJ⟩ := bound_of_isBounded hJB
  obtain ⟨κg, hκg, hgr⟩ := bound_of_isBounded hgB
  obtain ⟨hκH, hζH, hH⟩ := hA3
  have hcx : ∀ k, ‖P.c (R.x k)‖ ≤ κc := fun k => hc _ ⟨_, hX k, rfl⟩
  have hJx : ∀ k, ‖P.J (R.x k)‖ ≤ κJ := fun k => hJ _ ⟨_, hX k, rfl⟩
  have hgx : ∀ k, ‖P.grad (R.x k)‖ ≤ κg := fun k => hgr _ ⟨_, hX k, rfl⟩
  set a := min A.ω (1 / κJ ^ 2) with ha
  have ha0 : 0 < a := lt_min hω (by positivity)
  have haω : a ≤ A.ω := min_le_left _ _
  have haJ : a * κJ ^ 2 ≤ 1 := by
    have : a ≤ 1 / κJ ^ 2 := min_le_right _ _
    rw [le_div_iff₀ (by positivity)] at this; linarith
  -- bound on ‖J_kᵀ c_k‖
  have hw : ∀ k, ‖P.Jt (R.x k) (P.c (R.x k))‖ ≤ κJ * κc := by
    intro k
    calc ‖P.Jt (R.x k) (P.c (R.x k))‖ ≤ ‖P.Jt (R.x k)‖ * ‖P.c (R.x k)‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ κJ * κc := by
        rw [norm_Jt]; exact mul_le_mul (hJx k) (hcx k) (norm_nonneg _) hκJ.le
  -- the Cauchy-decrease facts (Lemma 1)
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
  -- bounds on g, v, u
  set G := κg + max M 1 with hG
  have hG0 : 0 < G := by positivity
  have hgk : ∀ k, ‖R.g k‖ ≤ G := by
    intro k
    have h1 : ‖R.g k - P.grad (R.x k)‖ ≤ max M 1 := by
      by_cases h : ‖R.g k - P.grad (R.x k)‖ ≤ 1
      · exact h.trans (le_max_right _ _)
      · push_neg at h
        have := hg k
        have : ‖R.g k - P.grad (R.x k)‖ ≤ M := by nlinarith
        exact this.trans (le_max_left _ _)
    have h2 : ‖R.g k‖ ≤ ‖P.grad (R.x k)‖ + ‖R.g k - P.grad (R.x k)‖ := by
      have := norm_add_le (P.grad (R.x k)) (R.g k - P.grad (R.x k))
      simpa using this
    linarith [hgx k]
  set V := A.ω * (κJ * κc) with hV
  have hV0 : 0 ≤ V := by positivity
  have hvk : ∀ k, ‖R.v k‖ ≤ V := by
    intro k
    obtain ⟨-, -, -, hvn, -⟩ := hR k
    exact hvn.trans (mul_le_mul_of_nonneg_left (hw k) hω.le)
  set U := (G + κH * V) / ζH with hU
  have hU0 : 0 ≤ U := by positivity
  have huk : ∀ k, ‖R.u k‖ ≤ U := by
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
  -- bound on the denominator of the merit-parameter trial value
  set B := G * (V + U) + κH * U ^ 2 + 1 with hB
  have hB0 : 0 < B := by positivity
  have hDk : ∀ k, ⟪R.g k, R.d k⟫_ℝ + ⟪R.u k, R.H k (R.u k)⟫_ℝ ≤ B := by
    intro k
    obtain ⟨-, -, -, -, -, -, -, hdd, -⟩ := hR k
    obtain ⟨-, hHn, -⟩ := hH k
    have hd : ‖R.d k‖ ≤ V + U := by
      rw [hdd]; exact (norm_add_le _ _).trans (add_le_add (hvk k) (huk k))
    have b1 : ⟪R.g k, R.d k⟫_ℝ ≤ G * (V + U) := by
      have := real_inner_le_norm (R.g k) (R.d k)
      exact this.trans (mul_le_mul (hgk k) hd (norm_nonneg _) hG0.le)
    have b2 : ⟪R.u k, R.H k (R.u k)⟫_ℝ ≤ κH * U ^ 2 := by
      have h1 := real_inner_le_norm (R.u k) (R.H k (R.u k))
      have h3 : ‖R.H k (R.u k)‖ ≤ κH * U :=
        ((R.H k).le_opNorm _).trans (mul_le_mul hHn (huk k) (norm_nonneg _) hκH.le)
      have h4 : ‖R.u k‖ * ‖R.H k (R.u k)‖ ≤ U * (κH * U) :=
        mul_le_mul (huk k) h3 (norm_nonneg _) hU0
      nlinarith
    linarith
  -- J_k d_k = J_k v_k
  have hJd : ∀ k, P.J (R.x k) (R.d k) = P.J (R.x k) (R.v k) := by
    intro k
    obtain ⟨-, -, -, -, -, -, hJu, hdd, -⟩ := hR k
    rw [hdd, map_add, hJu, add_zero]
  -- the key one-step analysis of the merit parameter rule
  -- (i) if the trial value is positive the update keeps τ above min(prev, (1-ετ) t)
  have hstep : ∀ k, ∀ tm : ℝ, 0 < tm →
      (∀ D : ℝ, 0 < D → D ≤ B → tm ≤ (1 - A.σ) *
        (‖P.c (R.x k)‖ - ‖P.c (R.x k) + P.J (R.x k) (R.v k)‖) / D) →
      min (prev R.τ A.τ₀ k) ((1 - A.ετ) * tm) ≤ R.τ k := by
    intro k tm htm hbound
    obtain ⟨-, -, -, -, -, -, -, -, hd0, hd1, -⟩ := hR k
    by_cases hd : R.d k = 0
    · rw [(hd0 hd).1]; exact min_le_left _ _
    obtain ⟨htr, -⟩ := hd1 hd
    set D := ⟪R.g k, R.d k⟫_ℝ + ⟪R.u k, R.H k (R.u k)⟫_ℝ with hDdef
    by_cases hD : D ≤ 0
    · rw [htr.1 hD]; exact min_le_left _ _
    push_neg at hD
    have h2 := htr.2 hD
    simp only [hJd k] at h2
    set t := (1 - A.σ) * (‖P.c (R.x k)‖ - ‖P.c (R.x k) + P.J (R.x k) (R.v k)‖) / D with ht
    have htt : tm ≤ t := hbound D hD (hDk k)
    by_cases hpt : prev R.τ A.τ₀ k ≤ t
    · rw [h2.1 hpt]; exact min_le_left _ _
    push_neg at hpt
    rw [h2.2 hpt]
    refine le_trans (min_le_right _ _) (le_min ?_ ?_)
    · have : 0 < 1 - A.ετ := by linarith
      exact mul_le_mul_of_nonneg_left (by linarith) this.le
    · have : 0 ≤ A.ετ * tm := mul_nonneg hετ.le htm.le
      linarith
  -- (ii) positivity of τ_k
  have hpos_step : ∀ k, 0 < prev R.τ A.τ₀ k → 0 < R.τ k := by
    intro k hp
    obtain ⟨⟨hβ0, -⟩, -, -, hvn, -, -, -, -, hd0, hd1, -⟩ := hR k
    by_cases hd : R.d k = 0
    · rw [(hd0 hd).1]; exact hp
    obtain ⟨htr, -, hxi, -⟩ := hd1 hd
    set D := ⟪R.g k, R.d k⟫_ℝ + ⟪R.u k, R.H k (R.u k)⟫_ℝ with hDdef
    by_cases hD : D ≤ 0
    · rw [htr.1 hD]; exact hp
    push_neg at hD
    have h2 := htr.2 hD
    simp only [hJd k] at h2
    set s := ‖P.c (R.x k)‖ - ‖P.c (R.x k) + P.J (R.x k) (R.v k)‖ with hsdef
    set t := (1 - A.σ) * s / D with ht
    by_cases hpt : prev R.τ A.τ₀ k ≤ t
    · rw [h2.1 hpt]; exact hp
    push_neg at hpt
    have hτk := h2.2 hpt
    have hs0 : 0 ≤ s := (hs k).1
    have ht0 : 0 ≤ t := by
      rw [ht]; exact div_nonneg (mul_nonneg (by linarith) hs0) hD.le
    by_cases htp : 0 < t
    · rw [hτk]; exact lt_min (mul_pos (by linarith) hp) htp
    exfalso
    have ht00 : t = 0 := le_antisymm (not_lt.1 htp) ht0
    have hτ0' : R.τ k = 0 := by
      rw [hτk, ht00]; exact min_eq_right (mul_pos (by linarith) hp).le
    have hs00 : s = 0 := by
      rw [ht] at ht00
      rcases div_eq_zero_iff.1 ht00 with h | h
      · rcases mul_eq_zero.1 h with h' | h'
        · linarith
        · exact h'
      · linarith
    have hw0 : ‖P.Jt (R.x k) (P.c (R.x k))‖ = 0 := by
      have := (hs k).2
      rw [← hsdef, hs00, mul_zero] at this
      have hpos : 0 < A.εv * a := mul_pos hεv ha0
      have : ‖P.Jt (R.x k) (P.c (R.x k))‖ ^ 2 ≤ 0 := by
        by_contra hh; push_neg at hh; nlinarith
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1
        (le_antisymm this (sq_nonneg _))
    have hv0 : ‖R.v k‖ = 0 := le_antisymm (by rw [hw0, mul_zero] at hvn; exact hvn)
      (norm_nonneg _)
    -- ξ_k ≤ trial value
    have hxiT : R.ξ k ≤ xiTrial P R k := by
      by_cases hh : prev R.ξ A.ξ₀ k ≤ xiTrial P R k
      · rw [hxi.1 hh]; exact hh
      · push_neg at hh; rw [hxi.2 hh]; exact min_le_right _ _
    have htrial : xiTrial P R k = 0 := by
      unfold xiTrial
      rw [if_pos (by rw [hv0]; simp [sq_nonneg]), hτ0', zero_mul, div_zero]
    obtain ⟨-, h28a, -⟩ := h28 k
    rw [hτ0'] at h28a
    have hξ : R.ξ k ≤ 0 := htrial ▸ hxiT
    have : 2 * (1 - A.η) * R.β k * R.ξ k * max 0 1 / (0 * A.L + A.Γ) ≤ 0 := by
      apply div_nonpos_of_nonpos_of_nonneg
      · have : 0 ≤ 2 * (1 - A.η) * R.β k := by
          have : 0 < 1 - A.η := by linarith
          positivity
        have h1 : 2 * (1 - A.η) * R.β k * R.ξ k ≤ 0 := mul_nonpos_of_nonneg_of_nonpos this hξ
        have h2 : (0:ℝ) ≤ max 0 1 := le_max_left _ _
        exact mul_nonpos_of_nonpos_of_nonneg h1 h2
      · linarith
    linarith
  have hpos : ∀ k, 0 < R.τ k := by
    intro k
    induction k with
    | zero => exact hpos_step 0 hτ0
    | succ j ih => exact hpos_step (j + 1) ih
  -- main argument
  intro γ hγ
  by_contra hfr
  rw [Filter.not_frequently] at hfr
  obtain ⟨K, hK⟩ := Filter.eventually_atTop.1 hfr
  set smin := A.εv * a * γ ^ 2 / (2 * κc) with hsmin
  have hsmin0 : 0 < smin := by positivity
  set tm := (1 - A.σ) * smin / B with htm
  have htm0 : 0 < tm := by
    have : 0 < 1 - A.σ := by linarith
    positivity
  have hbig : ∀ k, K ≤ k → min (prev R.τ A.τ₀ k) ((1 - A.ετ) * tm) ≤ R.τ k := by
    intro k hk
    apply hstep k tm htm0
    intro D hD hDB
    have hwk : γ ≤ ‖P.Jt (R.x k) (P.c (R.x k))‖ := not_lt.1 (hK k hk)
    obtain ⟨hs0, hs1⟩ := hs k
    set s := ‖P.c (R.x k)‖ - ‖P.c (R.x k) + P.J (R.x k) (R.v k)‖
    have hss : smin ≤ s := by
      rw [hsmin, div_le_iff₀ (by positivity)]
      have h1 : A.εv * a * γ ^ 2 ≤ A.εv * a * ‖P.Jt (R.x k) (P.c (R.x k))‖ ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hγ.le hwk 2) (by positivity)
      have h2 : 2 * ‖P.c (R.x k)‖ * s ≤ 2 * κc * s :=
        mul_le_mul_of_nonneg_right (by linarith [hcx k]) hs0
      nlinarith
    have hσ' : 0 < 1 - A.σ := by linarith
    rw [htm]
    calc (1 - A.σ) * smin / B ≤ (1 - A.σ) * smin / D :=
          div_le_div_of_nonneg_left (by positivity) hD hDB
      _ ≤ (1 - A.σ) * s / D :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hss hσ'.le) hD.le
  set m0 := min (prev R.τ A.τ₀ K) ((1 - A.ετ) * tm) with hm0
  have hm0pos : 0 < m0 := by
    have hpK : 0 < prev R.τ A.τ₀ K := by
      cases K with
      | zero => exact hτ0
      | succ j => exact hpos j
    have : 0 < 1 - A.ετ := by linarith
    exact lt_min hpK (by positivity)
  have hprev : ∀ j, m0 ≤ prev R.τ A.τ₀ (K + j) := by
    intro j
    induction j with
    | zero => exact min_le_left _ _
    | succ j ih =>
      show m0 ≤ R.τ (K + j)
      have := hbig (K + j) (Nat.le_add_right _ _)
      exact le_trans (le_min ih (min_le_right _ _)) this
  have hall : ∀ k, K ≤ k → m0 ≤ R.τ k := by
    intro k hk
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
    exact le_trans (le_min (hprev j) (min_le_right _ _)) (hbig (K + j) hk)
  have hev := (hτ.eventually (gt_mem_nhds hm0pos))
  obtain ⟨K2, hK2⟩ := Filter.eventually_atTop.1 hev
  have h1 := hK2 (max K K2) (le_max_right _ _)
  have h2 := hall (max K K2) (le_max_left _ _)
  linarith
