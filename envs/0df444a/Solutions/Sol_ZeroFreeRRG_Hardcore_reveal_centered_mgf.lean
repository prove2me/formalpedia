-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.reveal_centered_mgf
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T10:38:50.606219+00:00
-- url     : https://prove2.me/submissions/d2a2c018-7e2d-4e0d-994b-ac86f983d154

import Theorems.Thm_ZeroFreeRRG_Hardcore_bernoulli_signed_mgf
import Theorems.Thm_ZeroFreeRRG_Hardcore_reveal_moment_generating
import Mathlib
set_option autoImplicit false
open Set Filter MeasureTheory AFIsingKS ZeroFreeRRG.Hardcore
open scoped Classical BigOperators

theorem solution (n : ℕ) (s θ : ℝ) (z : Fin n → ℝ)
    (hs : 0 ≤ s) (hs1 : s ≤ 1) (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1/3)
    (hz : ∀ v, |z v| ≤ 1) :
    (∑ U : Finset (Fin n), revealProb s U *
      Real.exp (θ * ((∑ v ∈ U, z v) - s*(∑ v : Fin n, z v)))) ≤
        Real.exp ((3/4)*s*θ^2*n) := by
  classical
  have hexp : Real.exp (-(s*θ*(∑ v : Fin n, z v))) =
      ∏ v : Fin n, Real.exp (-(s*θ*z v)) := by
    rw [← Real.exp_sum, Finset.sum_neg_distrib, ← Finset.mul_sum]
  calc
    _ = (∑ U : Finset (Fin n), revealProb s U * Real.exp (θ*(∑ v ∈ U, z v))) *
        Real.exp (-(s*θ*(∑ v : Fin n, z v))) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro U hU
      rw [mul_assoc,← Real.exp_add]
      congr 2
      ring
    _ = (∏ v : Fin n, (s*Real.exp (θ*z v)+(1-s))) *
        (∏ v : Fin n, Real.exp (-(s*θ*z v))) := by
      rw [reveal_moment_generating n s θ z,hexp]
    _ = ∏ v : Fin n, ((1-s+s*Real.exp (θ*z v))*Real.exp (-(s*θ*z v))) := by
      rw [← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro v hv
      ring
    _ ≤ ∏ _v : Fin n, Real.exp ((3/4)*s*θ^2) := by
      apply Finset.prod_le_prod
      · intro v hv
        exact mul_nonneg (add_nonneg (sub_nonneg.mpr hs1) (mul_nonneg hs (Real.exp_pos _).le)) (Real.exp_pos _).le
      · intro v hv
        exact bernoulli_signed_mgf s θ (z v) hs hs1 hθ hθ1 (hz v)
    _ = Real.exp ((3/4)*s*θ^2*n) := by
      rw [← Real.exp_sum]
      congr 1
      simp
      ring
