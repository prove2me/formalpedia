-- Prove2me | solution 1 for ReciprocityTheory.GeometryOfNumbersTheory.integral_mono_sq_sphProb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:54:01.420312+00:00
-- url     : https://prove2.me/submissions/48494c4b-8ac3-49fb-a78f-a4a5c1cdd54f

import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_SphericalMonomials_MonomStA
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_SphericalMonomials_MonomSt
import Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_sphMonom_continuous_f
import Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_sphMonom_f_smul
import Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_sphMonom_gamma
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
theorem _root_.solution {D : ℕ} (a : Fin (D + 1) → ℕ) :
    ∫ z, ‖monoC a z‖ ^ 2 ∂(sphProb (D + 1)) = monoNormSq a := by
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  have e : ∀ z : Fin (D + 1) → ℂ,
      ((‖monoC a z‖ ^ 2 : ℝ) : ℂ) = starRingEnd ℂ (monoC a z) * monoC a z := fun z => by
    rw [Complex.conj_mul']; push_cast; rfl
  simp only [e]
  rw [sphMonom_integral_sphProb _ (sphMonom_continuous_f a a)]
  have hk := sphMonom_key (N := D + 1) (k := (∑ i, a i) + ∑ i, a i)
    (fun z => starRingEnd ℂ (monoC a z) * monoC a z) (sphMonom_f_smul a a)
  beta_reduce at hk
  have hG := integral_mono_sq_mul_exp a one_pos
  simp only [one_mul, one_pow, div_one] at hG
  have hG' : ∫ z, starRingEnd ℂ (monoC a z) * monoC a z * (Real.exp (-sqN z) : ℂ) =
      ((Real.pi ^ (D + 1) * ((∏ i, (a i).factorial : ℕ) : ℝ) : ℝ) : ℂ) := by
    rw [← hG, ← integral_complex_ofReal]
    congr 1; funext z
    rw [Complex.ofReal_mul, e]
  rw [hG', sphMonom_gamma D 0 0 rfl, sphMonom_gamma D (∑ i, a i) _ rfl] at hk
  have hR : (((((D + ∑ i, a i).factorial : ℕ) : ℝ) / 2 : ℝ) : ℂ) ≠ 0 := by
    norm_cast; positivity
  simp only [Nat.add_zero] at hk
  rw [eq_div_of_mul_eq hR hk.symm]
  unfold monoNormSq
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hf : (((D + ∑ i, a i).factorial : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  rw [add_comm (∑ i, a i) D]
  push_cast
  field_simp
end ReciprocityTheory.GeometryOfNumbersTheory
