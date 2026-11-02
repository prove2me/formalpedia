-- Prove2me | solution 1 for StochSQP.Vanishing.lemma_9_projection
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T11:51:03.845681+00:00
-- url     : https://prove2.me/submissions/c8e39678-6656-46b8-8825-237333c0c414

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
    (h28 : Cond28 A R) :
    ∀ k : ℕ, 0 < R.α k ∧ R.α k ≤ 1 ∧ (R.d k ≠ 0 → R.α k ≤ alphaSuff P A R k) := by
  obtain ⟨hL, hΓ, hτ0, hχ0, hζ0, hξ0, hω, hεv, hεv1, hσ, hσ1, hετ, hετ1, hεχ, hεζ, hεζ1,
    hεξ, hεξ1, hη, hη1, hθ⟩ := hA
  obtain ⟨-, -, -, -, -, -, -, -, -, hcB, -, hJB⟩ := hA1
  obtain ⟨κc, hκc, hc⟩ := bound_of_isBounded hcB
  obtain ⟨κJ, hκJ, hJ⟩ := bound_of_isBounded hJB
  have hcx : ∀ k, ‖P.c (R.x k)‖ ≤ κc := fun k => hc _ ⟨_, hX k, rfl⟩
  have hJx : ∀ k, ‖P.J (R.x k)‖ ≤ κJ := fun k => hJ _ ⟨_, hX k, rfl⟩
  set a := min A.ω (1 / κJ ^ 2) with ha
  have ha0 : 0 < a := lt_min hω (by positivity)
  have haω : a ≤ A.ω := min_le_left _ _
  have haJ : a * κJ ^ 2 ≤ 1 := by
    have : a ≤ 1 / κJ ^ 2 := min_le_right _ _
    rw [le_div_iff₀ (by positivity)] at this; linarith
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
  -- J_k d_k = J_k v_k
  have hJd : ∀ k, P.J (R.x k) (R.d k) = P.J (R.x k) (R.v k) := by
    intro k
    obtain ⟨-, -, -, -, -, -, hJu, hdd, -⟩ := hR k
    rw [hdd, map_add, hJu, add_zero]
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
  intro k
  obtain ⟨⟨hβ0, hβ1⟩, -, -, -, -, -, -, -, hd0, hd1, -⟩ := hR k
  by_cases hd : R.d k = 0
  · rw [(hd0 hd).2.2.2.2]
    exact ⟨one_pos, le_rfl, fun h => absurd hd h⟩
  obtain ⟨-, -, hxi, hal⟩ := hd1 hd
  have hτk := hpos k
  have hQ : 0 < R.τ k * A.L + A.Γ := by positivity
  obtain ⟨-, h28a, h28b⟩ := h28 k
  have hη' : 0 < 1 - A.η := by linarith
  have hN : 0 < 2 * (1 - A.η) * R.β k := by positivity
  have hξ : 0 < R.ξ k := by
    by_contra hh
    push_neg at hh
    have : 2 * (1 - A.η) * R.β k * R.ξ k * max (R.τ k) 1 / (R.τ k * A.L + A.Γ) ≤ 0 := by
      apply div_nonpos_of_nonpos_of_nonneg _ hQ.le
      exact mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hN.le hh)
        (le_trans zero_le_one (le_max_right _ _))
    linarith
  have hxiT : R.ξ k ≤ xiTrial P R k := by
    by_cases hh : prev R.ξ A.ξ₀ k ≤ xiTrial P R k
    · rw [hxi.1 hh]; exact hh
    · push_neg at hh; rw [hxi.2 hh]; exact min_le_right _ _
  have hd2 : 0 < ‖R.d k‖ ^ 2 := by
    have := norm_pos_iff.2 hd; positivity
  set Δ := deltaL P (R.x k) (R.τ k) (R.g k) (R.d k) with hΔ
  set lo := projLo A R k with hlo
  -- lo bounds
  have hlo_pos : 0 < lo ∧ lo ≤ 1 ∧
      lo ≤ 2 * (1 - A.η) * R.β k * Δ / ((R.τ k * A.L + A.Γ) * ‖R.d k‖ ^ 2) := by
    rw [hlo]; unfold projLo
    unfold xiTrial at hxiT
    by_cases hc : R.χ k * ‖R.v k‖ ^ 2 ≤ ‖R.u k‖ ^ 2
    · rw [if_pos hc]; rw [if_pos hc] at hxiT
      refine ⟨by positivity, ?_, ?_⟩
      · refine le_trans ?_ h28b
        apply div_le_div_of_nonneg_right _ hQ.le
        exact mul_le_mul_of_nonneg_left (le_max_left _ _) (by positivity)
      · rw [le_div_iff₀ (by positivity)] at hxiT
        rw [div_le_div_iff₀ hQ (by positivity)]
        have h1 : R.ξ k * R.τ k * ‖R.d k‖ ^ 2 ≤ Δ := by linarith
        have h2 := mul_le_mul_of_nonneg_left h1 (le_of_lt (mul_pos hN hQ))
        nlinarith
    · rw [if_neg hc]; rw [if_neg hc] at hxiT
      refine ⟨by positivity, ?_, ?_⟩
      · refine le_trans ?_ h28b
        apply div_le_div_of_nonneg_right _ hQ.le
        have : R.ξ k ≤ R.ξ k * max (R.τ k) 1 := by
          have := le_max_right (R.τ k) 1
          nlinarith
        have := mul_le_mul_of_nonneg_left this hN.le
        linarith
      · rw [le_div_iff₀ (by positivity)] at hxiT
        rw [div_le_div_iff₀ hQ (by positivity)]
        have h2 := mul_le_mul_of_nonneg_left hxiT (le_of_lt (mul_pos hN hQ))
        nlinarith
  obtain ⟨hl0, hl1, hlX⟩ := hlo_pos
  have hlS : lo ≤ alphaSuff P A R k := by
    unfold alphaSuff; exact le_min hlX hl1
  have hS1 : alphaSuff P A R k ≤ 1 := by unfold alphaSuff; exact min_le_right _ _
  have hhi : lo ≤ projHi A R k := by
    unfold projHi; rw [← hlo]; have := mul_nonneg hθ (sq_nonneg (R.β k)); linarith
  rw [hal]; unfold proj
  rw [← hlo]
  have hmin : min (alphaSuff P A R k) (projHi A R k) ≤ alphaSuff P A R k := min_le_left _ _
  have hmax : max lo (min (alphaSuff P A R k) (projHi A R k)) ≤ alphaSuff P A R k :=
    max_le hlS hmin
  refine ⟨lt_of_lt_of_le hl0 (le_max_left _ _), hmax.trans hS1, fun _ => hmax⟩
