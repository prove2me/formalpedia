-- Prove2me | solution 1 for QuadraticForm.exists_ternary_isotropic_mul_of_exists_of_exists
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/8fecf780-3eb2-5b33-8513-793ac4b87475

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_QuadraticForm_exists_ternary_isotropic_mul_of_exists_of_exists

set_option autoImplicit false

theorem solution
    (K : Type) [Field K] (t u u' : K)
    (h : ∃ z x y : K, ¬ (z = 0 ∧ x = 0 ∧ y = 0) ∧ z ^ 2 - t * x ^ 2 - u * y ^ 2 = 0)
    (h' : ∃ z x y : K, ¬ (z = 0 ∧ x = 0 ∧ y = 0) ∧ z ^ 2 - t * x ^ 2 - u' * y ^ 2 = 0) :
    ∃ z x y : K, ¬ (z = 0 ∧ x = 0 ∧ y = 0) ∧ z ^ 2 - t * x ^ 2 - (u * u') * y ^ 2 = 0 := by
  obtain ⟨z, x, y, hne, he⟩ := h
  obtain ⟨z', x', y', hne', he'⟩ := h'
  by_cases hy0 : y = 0
  · subst hy0
    refine ⟨z, x, 0, ?_, ?_⟩
    · rintro ⟨hz, hx, -⟩; exact hne ⟨hz, hx, rfl⟩
    · linear_combination he
  by_cases hy0' : y' = 0
  · subst hy0'
    refine ⟨z', x', 0, ?_, ?_⟩
    · rintro ⟨hz, hx, -⟩; exact hne' ⟨hz, hx, rfl⟩
    · linear_combination he'
  refine ⟨z * z' + t * x * x', z * x' + x * z', y * y', ?_, ?_⟩
  · rintro ⟨-, -, hyy⟩
    exact (mul_ne_zero hy0 hy0') hyy
  · linear_combination (z' ^ 2 - t * x' ^ 2) * he + (u * y ^ 2) * he'

end S_QuadraticForm_exists_ternary_isotropic_mul_of_exists_of_exists
end P2MW
export P2MW.S_QuadraticForm_exists_ternary_isotropic_mul_of_exists_of_exists (solution)
