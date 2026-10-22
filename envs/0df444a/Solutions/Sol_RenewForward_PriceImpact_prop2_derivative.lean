-- Prove2me | solution 1 for RenewForward.PriceImpact.prop2_derivative
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T12:12:16.973065+00:00
-- url     : https://prove2.me/submissions/f6a1f914-f666-4833-a3da-eff4a85abaaf

import Mathlib
import Definitions.Def_RenewForward_PriceImpact_Setting
import Definitions.Def_RenewForward_PriceImpact_ClosedForms

open RenewForward.PriceImpact

set_option maxRecDepth 20000 in
theorem solution (M : Params) (m : Moments) (hlam : 0 < M.lam) (hNR : 1 ≤ M.NR)
    (hs2T : 0 ≤ m.s2T) (hs2X : 0 ≤ m.s2X) (kW : ℝ) :
    0 < nuFwd M m kW ∧
    HasDerivAt (expSpotClosed M m)
      (spsPoly M m kW / (9 * (M.NR : ℝ) ^ 2 * nuFwd M m kW ^ 2)) kW := by
  have hN : (1 : ℝ) ≤ M.NR := by exact_mod_cast hNR
  have hN0 : (M.NR : ℝ) ≠ 0 := by positivity
  have hnu : ∀ k, 0 < nuFwd M m k := by
    intro k; unfold nuFwd
    have : 0 ≤ 27 * M.lam / M.NR * (2 * m.s2T + k ^ 2 * m.s2X) := by positivity
    have : 0 ≤ 8 * M.lam * (m.s2T + k ^ 2 * m.s2X) := by positivity
    linarith
  refine ⟨hnu kW, ?_⟩
  set A := M.a - M.c + m.muT with hA
  set B := M.a + 2 * M.c + m.muT with hB
  set N : ℝ := (M.NR : ℝ) with hNdef
  set W0 := N * (9 * A + 4 * M.lam * A * m.s2T + 2 * M.lam * m.tauT)
    + 9 * M.lam * ((B + m.muT - 3 * M.pR) * m.s2T + m.tauT) with hW0
  set W1 := N * (-9 * m.muX - 4 * M.lam * m.muX * m.s2T) - 9 * M.lam * m.muX * m.s2T with hW1
  set W2 := N * (4 * M.lam * A * m.s2X) + 9 * M.lam * m.muT * m.s2X with hW2
  set W3 := N * (-4 * M.lam * m.muX * m.s2X - 2 * M.lam * m.tauX) with hW3
  set V0 := N * (45 + 8 * M.lam * m.s2T) + 54 * M.lam * m.s2T with hV0
  set V2 := N * (8 * M.lam * m.s2X) + 27 * M.lam * m.s2X with hV2
  set w0 := W0 / N with hw0
  set w1 := W1 / N with hw1
  set w2 := W2 / N with hw2
  set w3 := W3 / N with hw3
  set n0 := V0 / N with hn0
  set n2 := V2 / N with hn2
  have eω : omegaFwd M m = fun k => w0 + w1 * k + w2 * k ^ 2 + w3 * k ^ 3 := by
    funext k; simp only [omegaFwd, meanQ0, meanP0, w0, w1, w2, w3, W0, W1, W2, W3, A, B, N]; field_simp; ring
  have eν : nuFwd M m = fun k => n0 + n2 * k ^ 2 := by
    funext k; simp only [nuFwd, n0, n2, V0, V2, N]; field_simp; ring
  have eE : expSpotClosed M m = fun k => (B - m.muX * k) / 3
      - 2 * (w0 + w1 * k + w2 * k ^ 2 + w3 * k ^ 3) / (3 * (n0 + n2 * k ^ 2)) := by
    funext k; simp only [expSpotClosed, meanP0, B]
    rw [show omegaFwd M m k = w0 + w1 * k + w2 * k ^ 2 + w3 * k ^ 3 from congrFun eω k,
      show nuFwd M m k = n0 + n2 * k ^ 2 from congrFun eν k]
  have hν' : n0 + n2 * kW ^ 2 ≠ 0 := by
    have := hnu kW; rw [eν] at this; exact this.ne'
  have hW : HasDerivAt (fun k => w0 + w1 * k + w2 * k ^ 2 + w3 * k ^ 3)
      (w1 + 2 * w2 * kW + 3 * w3 * kW ^ 2) kW := by
    have := (((hasDerivAt_const kW w0).add ((hasDerivAt_id' kW).const_mul w1)).add
      ((hasDerivAt_pow 2 kW).const_mul w2)).add ((hasDerivAt_pow 3 kW).const_mul w3)
    exact this.congr_deriv (by push_cast; ring)
  have hV : HasDerivAt (fun k => 3 * (n0 + n2 * k ^ 2)) (3 * (2 * n2 * kW)) kW := by
    have := (((hasDerivAt_const kW n0).add ((hasDerivAt_pow 2 kW).const_mul n2))).const_mul 3
    exact this.congr_deriv (by push_cast; ring)
  have hL : HasDerivAt (fun k => (B - m.muX * k) / 3) (-m.muX / 3) kW := by
    have := ((hasDerivAt_const kW B).sub ((hasDerivAt_id' kW).const_mul m.muX)).div_const 3
    exact this.congr_deriv (by ring)
  have h3ν : 3 * (n0 + n2 * kW ^ 2) ≠ 0 := by positivity
  have hD := hL.sub ((hW.const_mul 2).div hV h3ν)
  rw [eE]
  refine hD.congr_deriv ?_
  · have hsp : spsPoly M m kW = alpha0 M m + alpha1 M m * kW + alpha2 M m * kW ^ 2
        + alpha4 M m * kW ^ 4 := rfl
    rw [hsp, show nuFwd M m kW = n0 + n2 * kW ^ 2 from congrFun eν kW]
    have k0 : N * w0 = W0 := by simp only [w0]; field_simp
    have k1 : N * w1 = W1 := by simp only [w1]; field_simp
    have k2 : N * w2 = W2 := by simp only [w2]; field_simp
    have k3 : N * w3 = W3 := by simp only [w3]; field_simp
    have k4 : N * n0 = V0 := by simp only [n0]; field_simp
    have k5 : N * n2 = V2 := by simp only [n2]; field_simp
    have hsps : alpha0 M m + alpha1 M m * kW + alpha2 M m * kW ^ 2 + alpha4 M m * kW ^ 4
        = -3 * (m.muX * (V0 + V2 * kW ^ 2) ^ 2
          + 2 * (W1 + 2 * W2 * kW + 3 * W3 * kW ^ 2) * (V0 + V2 * kW ^ 2)
          - 2 * (W0 + W1 * kW + W2 * kW ^ 2 + W3 * kW ^ 3) * (2 * V2 * kW)) := by
      simp only [alpha0, alpha1, alpha2, alpha4, W0, W1, W2, W3, V0, V2, A, B, N]
      ring
    rw [hsps, ← k0, ← k1, ← k2, ← k3, ← k4, ← k5]
    clear_value w0 w1 w2 w3 n0 n2
    rw [show N * n0 + N * n2 * kW ^ 2 = N * (n0 + n2 * kW ^ 2) by ring]
    generalize n0 + n2 * kW ^ 2 = v at hν' ⊢
    rw [eq_div_iff (by positivity)]
    field_simp
    ring
