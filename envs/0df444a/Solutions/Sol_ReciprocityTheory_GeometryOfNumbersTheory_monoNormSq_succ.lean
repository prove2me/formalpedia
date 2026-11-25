-- Prove2me | solution 1 for ReciprocityTheory.GeometryOfNumbersTheory.monoNormSq_succ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:01:49.102924+00:00
-- url     : https://prove2.me/submissions/925d8d33-7146-4e67-ba9a-d9f0f3434002

import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_SphericalMonomials_MonoNormSq
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_SphericalMonomials_ChiPSt
import Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_chiPAux_sum_update_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.GeometryOfNumbersTheory
open Finset
namespace ReciprocityTheory.GeometryOfNumbersTheory
theorem _root_.solution {D : ℕ} (a : Fin (D + 1) → ℕ) :
    monoNormSq (Function.update a 0 (a 0 + 1)) =
      monoNormSq a * ((a 0 + 1 : ℝ) / ((∑ i, a i : ℕ) + D + 1 : ℝ)) := by
  have e0 : Function.update a 0 (a 0 + 1) 0 = a 0 + 1 := by simp
  have es : ∀ i : Fin D, Function.update a 0 (a 0 + 1) i.succ = a i.succ := fun i => by
    simp [Function.update_apply, Fin.succ_ne_zero]
  have hs : ∑ i, Function.update a 0 (a 0 + 1) i = (∑ i, a i) + 1 := by
    rw [chiPAux_sum_update_zero, Fin.sum_univ_succ a]
    ring
  have hp : (∏ i, (Function.update a 0 (a 0 + 1) i).factorial) = (a 0 + 1) * ∏ i, (a i).factorial := by
    simp only [Fin.prod_univ_succ, e0, es, Nat.factorial_succ]
    ring
  have hf : ((∑ i, a i) + 1 + D).factorial = ((∑ i, a i) + D + 1) * ((∑ i, a i) + D).factorial := by
    rw [show (∑ i, a i) + 1 + D = (∑ i, a i) + D + 1 by ring]
    exact Nat.factorial_succ _
  unfold monoNormSq
  rw [hs, hp, hf]
  push_cast
  have hF : (((∑ i, a i) + D).factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have hg : (∑ i, (a i : ℝ)) + D + 1 ≠ 0 := by positivity
  first
    | (rw [div_mul_div_comm, div_eq_div_iff (mul_ne_zero hg hF) (mul_ne_zero hF hg)]; ring)
    | (field_simp; ring)
end ReciprocityTheory.GeometryOfNumbersTheory
