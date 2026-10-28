-- Prove2me | solution 1 for QualityEncroach.Differ.benchmark_equilibrium
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T03:38:39.694988+00:00
-- url     : https://prove2.me/submissions/141404d4-8c94-4b30-9421-fac316abab7c

import Mathlib
import Definitions.Def_QualityEncroach_Differ_Benchmark

namespace Aux_QEW31
open QualityEncroach.Differ

noncomputable def qstar (w u : ℝ) : ℝ := max ((u - w) / (2 * u)) 0

lemma pay_eq (w u q : ℝ) : benchRetailerPayoff ⟨w, u, q⟩ = (u - w) * q - u * q ^ 2 := by
  unfold benchRetailerPayoff; ring

lemma retailer (w u : ℝ) (hu : 0 < u) :
    0 ≤ qstar w u ∧
    (∀ q, 0 ≤ q → benchRetailerPayoff ⟨w, u, q⟩ ≤ benchRetailerPayoff ⟨w, u, qstar w u⟩) ∧
    (∀ q0, 0 ≤ q0 → (∀ q, 0 ≤ q → benchRetailerPayoff ⟨w, u, q⟩ ≤ benchRetailerPayoff ⟨w, u, q0⟩) →
      q0 = qstar w u) := by
  refine ⟨le_max_right _ _, ?_⟩
  simp only [pay_eq]
  rcases lt_or_ge 0 (u - w) with h | h
  · obtain ⟨qs, hqs⟩ : ∃ qs, qs = (u - w) / (2 * u) := ⟨_, rfl⟩
    have hq : qstar w u = qs := by
      unfold qstar; rw [← hqs]; exact max_eq_left (by rw [hqs]; positivity)
    rw [hq]
    have hw : w = u - 2 * u * qs := by rw [hqs]; field_simp; ring
    have hid : ∀ q, (u - w) * qs - u * qs ^ 2 - ((u - w) * q - u * q ^ 2) = u * (q - qs) ^ 2 := by
      intro q; rw [hw]; ring
    constructor
    · intro q _
      have := hid q
      nlinarith [mul_nonneg hu.le (sq_nonneg (q - qs))]
    · intro q0 _ hmax
      have h1 := hmax qs (by rw [hqs]; positivity)
      have h2 := hid q0
      have h3 : u * (q0 - qs) ^ 2 ≤ 0 := by linarith
      have h4 : (q0 - qs) ^ 2 ≤ 0 := by
        by_contra hc; push_neg at hc; nlinarith [mul_pos hu hc]
      have h5 := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 (le_antisymm h4 (sq_nonneg _))
      linarith
  · have hq : qstar w u = 0 := by
      unfold qstar; apply max_eq_right
      exact div_nonpos_of_nonpos_of_nonneg h (by linarith)
    rw [hq]
    constructor
    · intro q hq0
      nlinarith [mul_nonneg hu.le (sq_nonneg q), mul_nonneg (neg_nonneg.2 h) hq0]
    · intro q0 hq0 hmax
      have h1 := hmax 0 le_rfl
      have h2 : u * q0 ^ 2 ≤ 0 := by nlinarith [mul_nonneg (neg_nonneg.2 h) hq0]
      have h4 : q0 ^ 2 ≤ 0 := by
        by_contra hc; push_neg at hc; nlinarith [mul_pos hu hc]
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 (le_antisymm h4 (sq_nonneg _))

lemma poly (U W : ℝ) (hU : 0 < U) (hWU : W < U) :
    27 * (W - U ^ 2) * (U - W) ≤ U ∧
      (U ≤ 27 * (W - U ^ 2) * (U - W) → U = 1 / 3 ∧ W = 2 / 9) := by
  have hid : 4 * (27 * (W - U ^ 2) * (U - W)) = 27 * (U - U ^ 2) ^ 2 - 27 * (2 * W - U - U ^ 2) ^ 2 := by
    ring
  have hfac : 27 * (U - U ^ 2) ^ 2 - 4 * U = U * (3 * U - 1) ^ 2 * (3 * U - 4) := by ring
  constructor
  · by_cases hW : W ≤ U ^ 2
    · nlinarith [mul_nonneg (sub_nonneg.2 hW) (sub_pos.2 hWU).le]
    · push_neg at hW
      have hU1 : U < 1 := by nlinarith
      have hneg : U * (3 * U - 1) ^ 2 * (3 * U - 4) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hU.le (sq_nonneg _)) (by linarith)
      nlinarith [sq_nonneg (2 * W - U - U ^ 2)]
  · intro key
    have hW : U ^ 2 < W := by
      by_contra hc; push_neg at hc
      nlinarith [mul_nonneg (sub_nonneg.2 hc) (sub_pos.2 hWU).le]
    have hU1 : U < 1 := by nlinarith
    have hneg : U * (3 * U - 1) ^ 2 * (3 * U - 4) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hU.le (sq_nonneg _)) (by linarith)
    have hsq : (2 * W - U - U ^ 2) ^ 2 ≤ 0 := by nlinarith
    have hd := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 (le_antisymm hsq (sq_nonneg _))
    have h3 : U * (3 * U - 1) ^ 2 * (3 * U - 4) = 0 := by nlinarith
    rcases mul_eq_zero.1 h3 with h | h
    · rcases mul_eq_zero.1 h with h' | h'
      · linarith
      · have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h'
        have hU3 : U = 1 / 3 := by linarith
        refine ⟨hU3, ?_⟩
        rw [hU3] at hd; linarith
    · linarith

/-- manufacturer payoff with the retailer's best response, scaled. -/
lemma mfr_bound (k w u : ℝ) (hk : 0 < k) (hu : 0 < u) :
    (w - k * u ^ 2) * qstar w u ≤ 1 / (54 * k) ∧
      (1 / (54 * k) ≤ (w - k * u ^ 2) * qstar w u → u = 1 / (3 * k) ∧ w = 2 / (9 * k)) := by
  rcases lt_or_ge 0 (u - w) with h | h
  · have hq : qstar w u = (u - w) / (2 * u) := by
      unfold qstar; exact max_eq_left (by positivity)
    rw [hq]
    have e : (w - k * u ^ 2) * ((u - w) / (2 * u)) = ((w - k * u ^ 2) * (u - w)) / (2 * u) := by ring
    rw [e]
    have hP := poly (k * u) (k * w) (mul_pos hk hu) (by nlinarith)
    have htr : 27 * (k * w - (k * u) ^ 2) * (k * u - k * w) = k * (27 * k * ((w - k * u ^ 2) * (u - w))) := by
      ring
    rw [htr] at hP
    constructor
    · rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have := hP.1
      have h2 : 27 * k * ((w - k * u ^ 2) * (u - w)) ≤ u := by
        by_contra hc; push_neg at hc; nlinarith [mul_lt_mul_of_pos_left hc hk]
      nlinarith
    · intro hle
      rw [div_le_div_iff₀ (by positivity) (by positivity)] at hle
      have h2 : k * u ≤ k * (27 * k * ((w - k * u ^ 2) * (u - w))) := by nlinarith
      obtain ⟨h3, h4⟩ := hP.2 h2
      constructor
      · field_simp; linarith
      · field_simp; linarith
  · have hq : qstar w u = 0 := by
      unfold qstar; apply max_eq_right
      exact div_nonpos_of_nonpos_of_nonneg h (by linarith)
    rw [hq, mul_zero]
    have hpos : 0 < 1 / (54 * k) := by positivity
    exact ⟨hpos.le, fun h' => absurd h' (not_le.2 hpos)⟩

end Aux_QEW31

open QualityEncroach.Differ Aux_QEW31 in
theorem solution (k : ℝ) (hk : 0 < k) :
    (∀ τ : BenchProfile, IsBenchSPE k τ →
      τ.u = 1 / (3 * k) ∧ τ.w = 2 / (9 * k) ∧ τ.path.qR = 1 / 6 ∧
      benchMfrPayoff k τ.path = 1 / (54 * k) ∧ benchRetailerPayoff τ.path = 1 / (108 * k)) ∧
    ∃ τ : BenchProfile, IsBenchSPE k τ := by
  have hu3 : 0 < 1 / (3 * k) := by positivity
  have hq3 : qstar (2 / (9 * k)) (1 / (3 * k)) = 1 / 6 := by
    unfold qstar
    have : (1 / (3 * k) - 2 / (9 * k)) / (2 * (1 / (3 * k))) = 1 / 6 := by
      field_simp; ring
    rw [this]; norm_num
  constructor
  · intro τ ⟨hR, hu0, hM⟩
    have hord : ∀ w u, 0 < u → τ.order w u = qstar w u := fun w u hu =>
      (retailer w u hu).2.2 _ (hR w u hu).1 (hR w u hu).2
    have hpath : benchMfrPayoff k τ.path = (τ.w - k * τ.u ^ 2) * qstar τ.w τ.u := by
      unfold benchMfrPayoff BenchProfile.path BenchProfile.outcomeAt
      simp only
      rw [hord _ _ hu0]
    have hlow := hM (2 / (9 * k)) (1 / (3 * k)) hu3
    have hval : benchMfrPayoff k (τ.outcomeAt (2 / (9 * k)) (1 / (3 * k))) = 1 / (54 * k) := by
      unfold benchMfrPayoff BenchProfile.outcomeAt
      simp only
      rw [hord _ _ hu3, hq3]
      field_simp; ring
    rw [hval, hpath] at hlow
    obtain ⟨hu, hw⟩ := (mfr_bound k τ.w τ.u hk hu0).2 hlow
    have hqR : τ.path.qR = 1 / 6 := by
      show τ.order τ.w τ.u = 1 / 6
      rw [hord _ _ hu0, hu, hw, hq3]
    refine ⟨hu, hw, hqR, ?_, ?_⟩
    · rw [hpath, hu, hw, hq3]; field_simp; ring
    · unfold benchRetailerPayoff
      rw [hqR]
      show (τ.u * (1 - 1 / 6) - τ.w) * (1 / 6) = 1 / (108 * k)
      rw [hu, hw]; field_simp; ring
  · refine ⟨⟨2 / (9 * k), 1 / (3 * k), qstar⟩, ⟨fun w u hu => ?_, hu3, fun w u hu => ?_⟩⟩
    · exact ⟨(retailer w u hu).1, (retailer w u hu).2.1⟩
    · unfold benchMfrPayoff BenchProfile.path BenchProfile.outcomeAt
      simp only
      rw [hq3]
      have := (mfr_bound k w u hk hu).1
      have hv : (2 / (9 * k) - k * (1 / (3 * k)) ^ 2) * (1 / 6) = 1 / (54 * k) := by
        field_simp; ring
      rw [hv]; exact this
