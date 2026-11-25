-- Prove2me | solution 1 for ReciprocityTheory.GeometryOfNumbersTheory.supSt_term
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:01:43.954734+00:00
-- url     : https://prove2.me/submissions/61124585-cace-44af-af30-79c9dbbe2c7d

import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_SphericalMonomials_MonomSt
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_PluriharmonicAnalysis_BergmanDefs
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_SphericalMonomials_SupStMonoNormSqPos

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
theorem _root_.solution {D n : ℕ} (a : Fin (D + 1) → ℕ) (ha : ∑ i, a i = n) (z : Fin (D + 1) → ℂ) :
    ‖monoC a z‖ ^ 2 / monoNormSq a =
      ((n + D).choose D : ℝ) * ((Nat.multinomial Finset.univ a : ℕ) *
        ∏ i, (‖z i‖ ^ 2) ^ a i) := by
  have hnorm : ‖monoC a z‖ ^ 2 = ∏ i, (‖z i‖ ^ 2) ^ a i := by
    simp only [monoC, norm_prod, norm_pow, ← Finset.prod_pow]
    exact Finset.prod_congr rfl fun i _ => by ring
  have hP : ((∏ i, (a i).factorial : ℕ) : ℝ) ≠ 0 := by
    have : 0 < ∏ i, (a i).factorial := Finset.prod_pos fun i _ => Nat.factorial_pos _
    exact_mod_cast this.ne'
  have hspec := Nat.multinomial_spec Finset.univ a
  rw [ha] at hspec
  have hm : ((Nat.multinomial Finset.univ a : ℕ) : ℝ) =
      (n.factorial : ℝ) / ((∏ i, (a i).factorial : ℕ) : ℝ) := by
    rw [eq_div_iff hP, mul_comm]
    exact_mod_cast hspec
  have hc : ((n + D).choose D : ℝ) = ((n + D).factorial : ℝ) / ((n.factorial : ℝ) * (D.factorial : ℝ)) := by
    rw [eq_div_iff (by positivity), ← mul_assoc]
    exact_mod_cast Nat.add_choose_mul_factorial_mul_factorial n D
  rw [hnorm, monoNormSq, ha, hm, hc]
  have h1 : (n.factorial : ℝ) ≠ 0 := by positivity
  have h2 : (D.factorial : ℝ) ≠ 0 := by positivity
  have h3 : ((n + D).factorial : ℝ) ≠ 0 := by positivity
  field_simp
end ReciprocityTheory.GeometryOfNumbersTheory
