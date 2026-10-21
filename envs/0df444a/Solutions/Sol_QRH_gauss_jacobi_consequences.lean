-- Prove2me | solution 1 for QRH.gauss_jacobi_consequences
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T13:07:23.212495+00:00
-- url     : https://prove2.me/submissions/ce5794b7-6128-40e6-9cea-6da7753dbd9d

import Mathlib
import Definitions.Def_QRH_arith
import Definitions.Def_QRH_sums
import Definitions.Def_QRH_lfun
universe u

open QRH

lemma g59q_star_mul {z : ℂ} (h : ‖z‖ = 1) : star z * z = 1 := by
  rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, h]; simp

lemma g59q_ne {z : ℂ} (h : ‖z‖ = 1) : z ≠ 0 := by
  intro h0; rw [h0, norm_zero] at h; exact zero_ne_one h

theorem solution (W : QRHWorld.{u}) (a b n : W.E)
    (hsn : W.IsSqf n) (hgn : W.Sgood n)
    (hsa : W.IsSqf a) (hga : W.Sgood a)
    (hsb : W.IsSqf b) (hgb : W.Sgood b)
    (hcop : ∀ d : W.E, d ∈ W.divs a → d ∈ W.divs b → d = W.one) :
    star (W.alpha n) * W.gamma 2 n * W.gamma 1 n
        = W.mu n * W.Gcl (W.cl n)
      ∧ W.mu n * W.gamma (-1) n
        = W.chiNeg n * (W.Gcl (W.cl n))⁻¹ * star (W.alpha n)
            * W.gamma 2 n
      ∧ W.chiNeg a * star (W.Gcl (W.cl a)) * W.Gcl (W.cl b)
            * W.Rcl (W.cl a) (W.cl b)
          = W.Gcl (W.mulC (W.cl b) (W.invC (W.cl a)))
      ∧ axi W (W.mul a b) = axi W a * axi W b * W.chi b a ^ 4 := by
  have hα := g59q_star_mul (W.alpha_abs n)
  have h12 := W.gamma_1_2 n hsn hgn
  refine ⟨?_, ?_, ?_, ?_⟩
  · calc star (W.alpha n) * W.gamma 2 n * W.gamma 1 n
        = star (W.alpha n) * (W.gamma 1 n * W.gamma 2 n) := by ring
      _ = W.mu n * W.Gcl (W.cl n) * (star (W.alpha n) * W.alpha n) := by rw [h12]; ring
      _ = _ := by rw [hα, mul_one]
  · have hm := W.mu_sqf n hsn
    have h1m := W.gamma_1_m1 n hsn hgn
    have hG := g59q_ne (W.Gcl_abs (W.cl n))
    have hg1 := g59q_ne (W.gamma_abs 1 n hsn hgn)
    -- multiply both sides by gamma 1 n * Gcl
    have : W.mu n * W.gamma (-1) n * (W.gamma 1 n * W.Gcl (W.cl n)) =
        W.chiNeg n * (W.Gcl (W.cl n))⁻¹ * star (W.alpha n) * W.gamma 2 n *
          (W.gamma 1 n * W.Gcl (W.cl n)) := by
      have e1 : W.mu n * W.gamma (-1) n * (W.gamma 1 n * W.Gcl (W.cl n)) =
          W.mu n * W.Gcl (W.cl n) * W.chiNeg n := by rw [← h1m]; ring
      have e2 : W.chiNeg n * (W.Gcl (W.cl n))⁻¹ * star (W.alpha n) * W.gamma 2 n *
          (W.gamma 1 n * W.Gcl (W.cl n)) =
          W.chiNeg n * ((W.Gcl (W.cl n))⁻¹ * W.Gcl (W.cl n)) * star (W.alpha n) *
            (W.gamma 1 n * W.gamma 2 n) := by ring
      rw [e1, e2, h12, inv_mul_cancel₀ hG]
      calc W.mu n * W.Gcl (W.cl n) * W.chiNeg n
          = W.chiNeg n * 1 * (star (W.alpha n) * W.alpha n) * W.mu n * W.Gcl (W.cl n) := by
            rw [hα]; ring
        _ = _ := by ring
    exact mul_right_cancel₀ (mul_ne_zero hg1 hG) this
  · have hGa := W.Gcl_abs (W.cl a)
    have hsG : star (W.Gcl (W.cl a)) = (W.Gcl (W.cl a))⁻¹ := by
      have := g59q_star_mul hGa
      exact eq_inv_of_mul_eq_one_left this
    have hR : W.Rcl (W.cl b) (W.invC (W.cl a)) = W.Rcl (W.cl a) (W.cl b) := by
      have h1 : W.Rcl (W.cl b) (W.invC (W.cl a)) * W.Rcl (W.cl b) (W.cl a) = 1 := by
        rw [← W.Rcl_mul_right, W.invC_mul_cancel, W.Rcl_one_right]
      rw [W.Rcl_symm (W.cl b) (W.cl a)] at h1
      rcases W.Rcl_real (W.cl a) (W.cl b) with h | h
      · rw [h] at h1 ⊢; simpa using h1
      · rw [h] at h1 ⊢; linear_combination -h1
    rw [W.Gcl_mul, W.Gcl_invC, hR, hsG]
    ring
  · unfold axi
    rw [W.gamma_2_mul a b hsa hsb hga hgb hcop, W.alpha_mul, W.xi_mul, star_mul',
      W.recip_cubic a b]
    ring
