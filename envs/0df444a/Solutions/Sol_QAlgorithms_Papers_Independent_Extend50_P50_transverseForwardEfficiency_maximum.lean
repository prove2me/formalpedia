-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Extend50.P50.transverseForwardEfficiency_maximum
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-31T00:22:51.832967+00:00
-- url     : https://prove2.me/submissions/93176c21-856d-4b0f-a9d3-e54f570f8c98

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P50

set_option autoImplicit false
open QAlgorithms.Papers.Independent.Extend50.P50

theorem solution :
    (∀ d : ℝ, 0 ≤ d → transverseForwardEfficiency d ≤ 4 * Real.exp (-2)) ∧
    transverseForwardEfficiency 2 = 4 * Real.exp (-2) := by
  constructor
  · intro d hd
    have h : d / 2 ≤ Real.exp (d / 2 - 1) := by
      linarith [Real.add_one_le_exp (d / 2 - 1)]
    have hsq := mul_self_le_mul_self (by positivity : 0 ≤ d / 2) h
    rw [← Real.exp_add] at hsq
    have he : d / 2 - 1 + (d / 2 - 1) = d - 2 := by ring
    rw [he] at hsq
    have hb : d ^ 2 ≤ 4 * Real.exp (d - 2) := by nlinarith
    unfold transverseForwardEfficiency
    calc
      d ^ 2 * Real.exp (-d) ≤ 4 * Real.exp (d - 2) * Real.exp (-d) :=
        mul_le_mul_of_nonneg_right hb (Real.exp_pos _).le
      _ = 4 * Real.exp (-2) := by
        rw [mul_assoc, ← Real.exp_add]
        congr 2
        ring
  · norm_num [transverseForwardEfficiency]


#print axioms solution
