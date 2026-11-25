-- Prove2me | solution 1 for ReciprocityTheory.GeometryOfNumbersTheory.integral_mono_mul_exp_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:36:42.539869+00:00
-- url     : https://prove2.me/submissions/a8cb076a-ddfd-42e8-a06f-84b7aaf19b10

import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_SphericalMonomials_MonoNormSq
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_SphericalMonomials_GaussSt
import Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_integral_conj_pow_mul_pow_mul_exp_of_ne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.GeometryOfNumbersTheory
open MeasureTheory
namespace ReciprocityTheory.GeometryOfNumbersTheory
theorem _root_.solution {N : ℕ} {a b : Fin N → ℕ} (hab : a ≠ b) {t : ℝ} (ht : 0 < t) :
    ∫ z : Fin N → ℂ, starRingEnd ℂ (monoC a z) * monoC b z * (Real.exp (-(t * sqN z)) : ℂ) = 0 := by
  simp_rw [gs_prod]
  rw [integral_fintype_prod_volume_eq_prod (fun i (w : ℂ) =>
    starRingEnd ℂ (w ^ a i) * w ^ b i * (Real.exp (-(t * ‖w‖ ^ 2)) : ℂ))]
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hab
  exact Finset.prod_eq_zero (Finset.mem_univ i) (integral_conj_pow_mul_pow_mul_exp_of_ne hi t)
end ReciprocityTheory.GeometryOfNumbersTheory
