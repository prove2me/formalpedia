-- Prove2me | solution 1 for ReciprocityTheory.GeometryOfNumbersTheory.integral_mono_sphProb_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:20:29.110902+00:00
-- url     : https://prove2.me/submissions/6eeda641-d09b-43d0-b366-ab2d6d3a70fe

import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_SphericalMonomials_MonomStA
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_SphericalMonomials_MonomSt
import Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_integral_mono_mul_exp_of_ne
import Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_sphMonom_continuous_f
import Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_sphMonom_f_smul
import Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_sphMonom_integral_sphProb
import Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_sphMonom_key


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
theorem _root_.solution {D : ℕ} {a b : Fin (D + 1) → ℕ} (hab : a ≠ b) :
    ∫ z, starRingEnd ℂ (monoC a z) * monoC b z ∂(sphProb (D + 1)) = 0 := by
  have hk := sphMonom_key (N := D + 1) (k := (∑ i, a i) + ∑ i, b i)
    (fun z => starRingEnd ℂ (monoC a z) * monoC b z) (sphMonom_f_smul a b)
  beta_reduce at hk
  have hG := integral_mono_mul_exp_of_ne hab one_pos
  simp only [one_mul] at hG
  rw [hG, zero_mul] at hk
  rw [sphMonom_integral_sphProb _ (sphMonom_continuous_f a b)]
  rcases mul_eq_zero.mp hk.symm with h | h
  · rw [h, mul_zero]
  · exfalso
    norm_cast at h
    exact (div_pos (Real.Gamma_pos_of_pos (by positivity)) two_pos).ne' h
end ReciprocityTheory.GeometryOfNumbersTheory
