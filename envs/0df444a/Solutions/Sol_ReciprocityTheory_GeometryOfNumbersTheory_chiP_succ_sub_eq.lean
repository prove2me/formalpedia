-- Prove2me | solution 1 for ReciprocityTheory.GeometryOfNumbersTheory.chiP_succ_sub_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:15:26.320949+00:00
-- url     : https://prove2.me/submissions/bf11df62-3662-4bd4-8130-fbea9c951856

import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_SphericalMonomials_MonoNormSq
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_SphericalMonomials_ChiPSt
import Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_monoNormSq_pos
import Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_monoNormSq_succ
import Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_chiPAux_sum_split

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
theorem _root_.solution (D n : ℕ) :
    chiP D (n + 1) - chiP D n = (1 / 2) *
      (∑ a ∈ Finset.Nat.antidiagonalTuple (D + 1) n, -Real.log ((a 0 + 1 : ℝ) / ((n : ℝ) + D + 1)) +
       ∑ b ∈ (Finset.Nat.antidiagonalTuple (D + 1) (n + 1)).filter (fun b => b 0 = 0),
          -Real.log (monoNormSq b)) := by
  unfold chiP
  rw [chiPAux_sum_split D n (fun b => Real.log (monoNormSq b))]
  have hstep : ∀ a ∈ Finset.Nat.antidiagonalTuple (D + 1) n,
      Real.log (monoNormSq (Function.update a 0 (a 0 + 1))) =
        Real.log (monoNormSq a) + Real.log ((a 0 + 1 : ℝ) / ((n : ℝ) + D + 1)) := by
    intro a ha
    have ha' := Finset.Nat.mem_antidiagonalTuple.mp ha
    rw [monoNormSq_succ, ha', Real.log_mul (monoNormSq_pos a).ne' (by positivity)]
  rw [Finset.sum_congr rfl hstep, Finset.sum_add_distrib]
  simp only [Finset.sum_neg_distrib]
  ring
end ReciprocityTheory.GeometryOfNumbersTheory
