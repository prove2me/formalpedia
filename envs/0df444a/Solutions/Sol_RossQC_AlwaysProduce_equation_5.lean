-- Prove2me | solution 1 for RossQC.AlwaysProduce.equation_5
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T20:00:13.085265+00:00
-- url     : https://prove2.me/submissions/98e6e76d-2770-472a-b6d2-22f29813f2d2

import Mathlib
import Definitions.Def_RossQC_AlwaysProduce_Model
open RossQC.AlwaysProduce

private theorem iter (M : Model) (n : ℕ) (P : ℝ) :
    (M.T^[n]) P = 1 - (1-P)*(1-M.π)^n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, Model.T, pow_succ]
    ring

theorem solution (M : Model)
    (hβ0 : 0 < M.β) (hβ1 : M.β < 1)
    (hπ0 : 0 ≤ M.π) (hπ1 : M.π ≤ 1)
    (hC0 : 0 < M.C) (hCI : M.C < M.I) (hIR : M.I < M.R) :
    ∀ P ∈ Set.Icc (0 : ℝ) 1,
      M.psi P = M.C / (1 - M.β) -
        M.C * (1 - P) / (1 - M.β * (1 - M.π)) := by
  intro P hP
  have hq0 : 0 ≤ M.β * (1-M.π) := mul_nonneg hβ0.le (sub_nonneg.mpr hπ1)
  have hq1 : M.β * (1-M.π) < 1 := by
    nlinarith [mul_nonneg hβ0.le hπ0]
  have hβ : |M.β| < 1 := by rw [abs_of_pos hβ0]; exact hβ1
  have hq : |M.β*(1-M.π)| < 1 := by rw [abs_of_nonneg hq0]; exact hq1
  have h1 := (hasSum_geometric_of_abs_lt_one hβ).mul_left M.C
  have h2 := (hasSum_geometric_of_abs_lt_one hq).mul_left (M.C*(1-P))
  have hs := h1.sub h2
  have he : (fun n : ℕ => M.β^n * (M.C*(M.T^[n]) P)) =
      (fun n : ℕ => M.C * M.β^n - (M.C*(1-P))*(M.β*(1-M.π))^n) := by
    funext n
    rw [iter, mul_pow]
    ring
  unfold Model.psi
  rw [he]
  convert hs.tsum_eq using 1 <;> simp only [div_eq_mul_inv]

#print axioms solution
