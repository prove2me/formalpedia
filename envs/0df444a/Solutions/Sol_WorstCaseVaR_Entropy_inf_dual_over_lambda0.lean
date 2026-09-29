-- Prove2me | solution 1 for WorstCaseVaR.Entropy.inf_dual_over_lambda0
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T23:40:56.214302+00:00
-- url     : https://prove2.me/submissions/4d91cda3-cc25-4dc8-8663-77ce9bcde26b

import Mathlib
import Definitions.Def_WorstCaseVaR_Entropy_Basic

namespace WorstCaseVaR.Entropy

theorem aux_idol_K_pos (φ lam : ℝ) (hlam : 0 < lam) (hφ0 : 0 ≤ φ) :
    0 < (Real.exp (1 / lam) - 1) * φ + 1 := by
  have h1 : 0 ≤ Real.exp (1 / lam) - 1 := by
    have : 1 ≤ Real.exp (1 / lam) := Real.one_le_exp (by positivity)
    linarith
  have := mul_nonneg h1 hφ0
  linarith

end WorstCaseVaR.Entropy

open WorstCaseVaR.Entropy

theorem solution (d φ lam : ℝ) (hlam : 0 < lam) (hφ0 : 0 ≤ φ) (hφ1 : φ ≤ 1) :
    IsLeast
      (Set.range fun lam0 : ℝ =>
        lam0 + lam * d + lam * Real.exp (-(lam0 / lam) - 1) * ((Real.exp (1 / lam) - 1) * φ + 1))
      (dualValue d φ lam) := by
  set K := (Real.exp (1 / lam) - 1) * φ + 1 with hK
  have hKpos : 0 < K := aux_idol_K_pos φ lam hlam hφ0
  have hlam0 : lam ≠ 0 := hlam.ne'
  unfold dualValue
  rw [← hK]
  constructor
  · refine ⟨lam * (Real.log K - 1), ?_⟩
    simp only
    have e1 : -(lam * (Real.log K - 1) / lam) - 1 = -Real.log K := by
      field_simp
      ring
    rw [e1, Real.exp_neg, Real.exp_log hKpos]
    field_simp
    ring
  · rintro y ⟨lam0, rfl⟩
    simp only
    set s := -(lam0 / lam) - 1 + Real.log K with hs
    have hes : Real.exp (-(lam0 / lam) - 1) * K = Real.exp s := by
      rw [hs, Real.exp_add, Real.exp_log hKpos]
    have hlin : lam0 = lam * (lam0 / lam) := by field_simp
    have key : s + 1 ≤ Real.exp s := Real.add_one_le_exp s
    have hprod : 0 ≤ lam * (Real.exp s - s - 1) := mul_nonneg hlam.le (by linarith)
    have : lam * Real.exp (-(lam0 / lam) - 1) * K = lam * Real.exp s := by
      rw [mul_assoc, hes]
    rw [this]
    have hexp : lam * (Real.exp s - s - 1) = lam * Real.exp s - lam * s - lam := by ring
    have hs' : lam * s = -lam0 - lam + lam * Real.log K := by
      rw [hs]; field_simp
    nlinarith [hprod, hexp, hs']
