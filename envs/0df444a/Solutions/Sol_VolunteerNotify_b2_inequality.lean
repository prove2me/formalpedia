-- Prove2me | solution 1 for VolunteerNotify.b2_inequality
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T15:33:56.210198+00:00
-- url     : https://prove2.me/submissions/75d480a6-6a3e-4c03-aee4-ecd99fc65266

import Mathlib
import Definitions.Def_VolunteerNotify_lpValue

open VolunteerNotify in
theorem solution {V S T : ℕ} (I : Instance V S T) (x : Decision V S T)
    (hx : x ∈ feasibleSet I) (s : Fin S) (t : Fin T) :
    (1 - 1 / Real.exp 1) * min (∑ v, x v s t * I.p v s) 1 ≤
      1 - ∏ v, (1 - x v s t * I.p v s) := by
  have ha : ∀ v, 0 ≤ x v s t * I.p v s ∧ x v s t * I.p v s ≤ 1 := by
    intro v
    have h1 := (hx v).1 s t
    have h2 := I.p_mem v s
    exact ⟨mul_nonneg h1.1 h2.1, mul_le_one₀ h1.2 h2.1 h2.2⟩
  have hprod : ∏ v, (1 - x v s t * I.p v s) ≤ Real.exp (-∑ v, x v s t * I.p v s) := by
    rw [← Finset.sum_neg_distrib, Real.exp_sum]
    exact Finset.prod_le_prod (fun v _ => by linarith [(ha v).2])
      (fun v _ => by have := Real.add_one_le_exp (-(x v s t * I.p v s)); linarith)
  have hA : 0 ≤ ∑ v, x v s t * I.p v s := Finset.sum_nonneg (fun v _ => (ha v).1)
  have hconc : ∀ A : ℝ, 0 ≤ A → (1 - Real.exp (-1)) * min A 1 ≤ 1 - Real.exp (-A) := by
    intro A hA0
    rcases le_total 1 A with h | h
    · rw [min_eq_right h]
      have : Real.exp (-A) ≤ Real.exp (-1) := Real.exp_le_exp.mpr (by linarith)
      linarith
    · rw [min_eq_left h]
      have key := convexOn_exp.2 (Set.mem_univ (0:ℝ)) (Set.mem_univ (-1:ℝ))
        (by linarith : (0:ℝ) ≤ 1 - A) hA0 (by ring)
      rw [smul_eq_mul, smul_eq_mul, smul_eq_mul, smul_eq_mul, mul_zero, zero_add, Real.exp_zero,
        mul_one, show A * -1 = -A by ring] at key
      nlinarith
  have h := hconc _ hA
  rw [Real.exp_neg 1, ← one_div] at h
  linarith
