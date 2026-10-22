-- Prove2me | solution 1 for RenewForward.PriceImpact.prop2_forward
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T12:15:56.362393+00:00
-- url     : https://prove2.me/submissions/e44b4a8d-64a0-4319-95ab-068e97251b60

import Mathlib
import Definitions.Def_RenewForward_PriceImpact_Setting
import Definitions.Def_RenewForward_PriceImpact_ClosedForms

open RenewForward.PriceImpact

private lemma ev6_aux (c i : ℝ) (k : ℝ) (n : ℕ) (hk : 1 ≤ k) (hn : n ≤ 5) (hi : i = c * k ^ n) :
    -(|c| * k ^ 5) ≤ i := by
  have hp : k ^ n ≤ k ^ 5 := pow_le_pow_right₀ hk hn
  have h1 : |i| ≤ |c| * k ^ 5 := by
    rw [hi, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ k ^ n)]
    exact mul_le_mul_of_nonneg_left hp (abs_nonneg c)
  have := neg_abs_le i
  linarith

private lemma ev6 (c0 c1 c2 c3 c4 c5 c6 : ℝ) (h : 0 < c6) :
    ∃ K : ℝ, ∀ k, K ≤ k →
      0 < c0 + c1 * k + c2 * k ^ 2 + c3 * k ^ 3 + c4 * k ^ 4 + c5 * k ^ 5 + c6 * k ^ 6 := by
  set S := |c0| + |c1| + |c2| + |c3| + |c4| + |c5|
  have hS : 0 ≤ S := by positivity
  refine ⟨1 + S / c6, fun k hk => ?_⟩
  have hk1 : 1 ≤ k := by have : 0 ≤ S / c6 := by positivity
                         linarith
  have e0 := ev6_aux c0 c0 k 0 hk1 (by norm_num) (by simp)
  have e1 := ev6_aux c1 (c1 * k) k 1 hk1 (by norm_num) (by simp)
  have e2 := ev6_aux c2 (c2 * k ^ 2) k 2 hk1 (by norm_num) rfl
  have e3 := ev6_aux c3 (c3 * k ^ 3) k 3 hk1 (by norm_num) rfl
  have e4 := ev6_aux c4 (c4 * k ^ 4) k 4 hk1 (by norm_num) rfl
  have e5 := ev6_aux c5 (c5 * k ^ 5) k 5 hk1 (by norm_num) rfl
  have hck : c6 * k ≥ c6 + S := by
    have : c6 * (1 + S / c6) = c6 + S := by field_simp
    nlinarith
  have hk5 : 0 < k ^ 5 := by positivity
  have : c6 * k ^ 6 - S * k ^ 5 = k ^ 5 * (c6 * k - S) := by ring
  have : 0 < k ^ 5 * (c6 * k - S) := mul_pos hk5 (by linarith)
  nlinarith

theorem solution (M : Params) (m : Moments) (hlam : 0 < M.lam) (hNR : 1 ≤ M.NR)
    (hs2X : 0 < m.s2X) (hs2T : 0 ≤ m.s2T) (hpos : 0 < 2 * m.muX * m.s2X + m.tauX) :
    ∃ kf : ℝ, ∀ kW : ℝ, kf ≤ kW → 0 < deriv (fwdPriceClosed M m) kW := by
  have hN : (1 : ℝ) ≤ M.NR := by exact_mod_cast hNR
  have hN0 : (M.NR : ℝ) ≠ 0 := by positivity
  set N : ℝ := (M.NR : ℝ) with hNdef
  set B := M.a + 2 * M.c + m.muT with hB
  set A := M.a - M.c + m.muT with hA
  set a0 := 3 * N * B + M.lam * ((B + m.muT - 3 * M.pR) * m.s2T + m.tauT) with ha0
  set a1 := -3 * N * m.muX - M.lam * m.muX * m.s2T with ha1
  set a2 := M.lam * m.muT * m.s2X with ha2
  set b0 := 3 * N + 2 * M.lam * m.s2T with hb0
  set b2 := M.lam * m.s2X with hb2
  set W0 := N * (9 * A + 4 * M.lam * A * m.s2T + 2 * M.lam * m.tauT)
    + 9 * M.lam * ((B + m.muT - 3 * M.pR) * m.s2T + m.tauT) with hW0
  set W1 := N * (-9 * m.muX - 4 * M.lam * m.muX * m.s2T) - 9 * M.lam * m.muX * m.s2T with hW1
  set W2 := N * (4 * M.lam * A * m.s2X) + 9 * M.lam * m.muT * m.s2X with hW2
  set W3 := N * (-4 * M.lam * m.muX * m.s2X - 2 * M.lam * m.tauX) with hW3
  set V0 := N * (45 + 8 * M.lam * m.s2T) + 54 * M.lam * m.s2T with hV0
  set V2 := N * (8 * M.lam * m.s2X) + 27 * M.lam * m.s2X with hV2
  have hNp : 0 < N := by positivity
  have hVpos : ∀ k : ℝ, 0 < V0 + V2 * k ^ 2 := by
    intro k
    have : 0 < V0 := by simp only [V0]; positivity
    have : 0 ≤ V2 := by simp only [V2]; positivity
    positivity
  have hω : ∀ k, omegaFwd M m k = (W0 + W1 * k + W2 * k ^ 2 + W3 * k ^ 3) / N := by
    intro k; simp only [omegaFwd, meanQ0, meanP0, W0, W1, W2, W3, A, B, N]; field_simp; ring
  have hν : ∀ k, nuFwd M m k = (V0 + V2 * k ^ 2) / N := by
    intro k; simp only [nuFwd, V0, V2, N]; field_simp; ring
  have haF : ∀ k, aF M m k = (a0 + a1 * k + a2 * k ^ 2) / (9 * N) := by
    intro k; simp only [aF, meanP0, a0, a1, a2, B, N]; field_simp; ring
  have hbF : ∀ k, bF M m k = (b0 + b2 * k ^ 2) / (9 * N) := by
    intro k; simp only [bF, b0, b2, N]; field_simp; ring
  have eF : fwdPriceClosed M m = fun k => ((a0 + a1 * k + a2 * k ^ 2)
      - 2 * (b0 + b2 * k ^ 2) * (W0 + W1 * k + W2 * k ^ 2 + W3 * k ^ 3) / (V0 + V2 * k ^ 2))
      / (9 * N) := by
    funext k
    simp only [fwdPriceClosed]
    rw [haF, hbF, hω, hν]
    have := (hVpos k).ne'
    field_simp
  clear_value a0 a1 a2 b0 b2 W0 W1 W2 W3 V0 V2
  set c0 := V0 ^ 2 * a1 - 2 * V0 * W1 * b0
  set c1 := 2 * V0 ^ 2 * a2 - 4 * V0 * W0 * b2 - 4 * V0 * W2 * b0 + 4 * V2 * W0 * b0
  set c2 := 2 * V0 * V2 * a1 - 6 * V0 * W1 * b2 - 6 * V0 * W3 * b0 + 2 * V2 * W1 * b0
  set c3 := 4 * V0 * V2 * a2 - 8 * V0 * W2 * b2
  set c4 := -10 * V0 * W3 * b2 + V2 ^ 2 * a1 - 2 * V2 * W1 * b2 - 2 * V2 * W3 * b0
  set c5 := 2 * V2 ^ 2 * a2 - 4 * V2 * W2 * b2
  set c6 := -6 * V2 * W3 * b2
  have hD : ∀ k, HasDerivAt (fwdPriceClosed M m)
      ((c0 + c1 * k + c2 * k ^ 2 + c3 * k ^ 3 + c4 * k ^ 4 + c5 * k ^ 5 + c6 * k ^ 6)
        / (V0 + V2 * k ^ 2) ^ 2 / (9 * N)) k := by
    intro k
    rw [eF]
    have hb : HasDerivAt (fun k => 2 * (b0 + b2 * k ^ 2)) (2 * (2 * b2 * k)) k := by
      have := (((hasDerivAt_const k b0).add ((hasDerivAt_pow 2 k).const_mul b2))).const_mul 2
      exact this.congr_deriv (by push_cast; ring)
    have hW : HasDerivAt (fun k => W0 + W1 * k + W2 * k ^ 2 + W3 * k ^ 3)
        (W1 + 2 * W2 * k + 3 * W3 * k ^ 2) k := by
      have := (((hasDerivAt_const k W0).add ((hasDerivAt_id' k).const_mul W1)).add
        ((hasDerivAt_pow 2 k).const_mul W2)).add ((hasDerivAt_pow 3 k).const_mul W3)
      exact this.congr_deriv (by push_cast; ring)
    have hV : HasDerivAt (fun k => V0 + V2 * k ^ 2) (2 * V2 * k) k := by
      have := ((hasDerivAt_const k V0).add ((hasDerivAt_pow 2 k).const_mul V2))
      exact this.congr_deriv (by push_cast; ring)
    have hA' : HasDerivAt (fun k => a0 + a1 * k + a2 * k ^ 2) (a1 + 2 * a2 * k) k := by
      have := ((hasDerivAt_const k a0).add ((hasDerivAt_id' k).const_mul a1)).add
        ((hasDerivAt_pow 2 k).const_mul a2)
      exact this.congr_deriv (by push_cast; ring)
    have hall := (hA'.sub ((hb.mul hW).div hV (hVpos k).ne')).div_const (9 * N)
    refine hall.congr_deriv ?_
    have hv := (hVpos k).ne'
    simp only [Pi.mul_apply, c0, c1, c2, c3, c4, c5, c6]
    congr 1
    rw [eq_div_iff (pow_ne_zero 2 hv), sub_mul, div_mul_cancel₀ _ (pow_ne_zero 2 hv)]
    ring
  have hc6 : 0 < c6 := by
    simp only [c6]
    rw [hV2, hW3, hb2]
    have h1 : 0 < N * (8 * M.lam * m.s2X) + 27 * M.lam * m.s2X := by positivity
    have h2 : 0 < 2 * N * M.lam * (2 * m.muX * m.s2X + m.tauX) := by positivity
    have h3 : 0 < M.lam * m.s2X := by positivity
    have : N * (-4 * M.lam * m.muX * m.s2X - 2 * M.lam * m.tauX)
        = -(2 * N * M.lam * (2 * m.muX * m.s2X + m.tauX)) := by ring
    rw [this]
    have := mul_pos (mul_pos h1 h2) h3
    nlinarith
  obtain ⟨K, hK⟩ := ev6 c0 c1 c2 c3 c4 c5 c6 hc6
  refine ⟨K, fun k hk => ?_⟩
  rw [(hD k).deriv]
  have := hK k hk
  have := hVpos k
  positivity
