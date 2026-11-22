-- Prove2me | solution 1 for ReciprocityTheory.Gal.eq_of_pow_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:32:01.649857+00:00
-- url     : https://prove2.me/submissions/a23f0815-4754-4a49-85e9-eef62e47d0e7

import Mathlib
import Definitions.Def_ReciprocityTheory_GaloisValuations_GlobalA
import Theorems.Thm_ReciprocityTheory_Gal_eq_one_of_pow_eq_one
import Theorems.Thm_ReciprocityTheory_Gal_valuation_eq_one_of_pow_eq_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Pointwise
open ReciprocityTheory ReciprocityTheory.Gal
variable {Ω : Type*} [Field Ω]
namespace ReciprocityTheory.Gal
theorem _root_.solution (A : ValuationSubring Ω) {N : ℕ} (hN : ¬ A.valuation (N : Ω) < 1)
    {a b : Ω} (ha : a ^ N = 1) (hb : b ^ N = 1) (h : A.valuation (a - b) < 1) : a = b := by
  have hN0 : N ≠ 0 := by
    rintro rfl
    apply hN
    simp
  have hb0 : b ≠ 0 := by
    rintro rfl
    simp [hN0] at hb
  have hvb := valuation_eq_one_of_pow_eq_one A hN0 hb
  have hξ : (a / b) ^ N = 1 := by rw [div_pow, ha, hb, div_one]
  have hξ1 : A.valuation (a / b - 1) < 1 := by
    rw [div_sub_one hb0, Valuation.map_div, hvb, div_one]
    exact h
  have h2 := eq_one_of_pow_eq_one A hN hξ hξ1
  rwa [div_eq_one_iff_eq hb0] at h2
end ReciprocityTheory.Gal
