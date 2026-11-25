-- Prove2me | solution 1 for ReciprocityTheory.GeometryOfNumbersTheory.chiP_succ_sub_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:17:10.355859+00:00
-- url     : https://prove2.me/submissions/f425a925-3c30-446e-8179-33c766714738

import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_SphericalMonomials_MonoNormSq
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_SphericalMonomials_ChiPSt
import Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_chiP_succ_sub_eq
import Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_chiPAux_neg_log_step_mem
import Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_chiPAux_neg_log_monoNormSq_nonneg

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
theorem _root_.solution (D n : ℕ) : 0 ≤ chiP D (n + 1) - chiP D n := by
  rw [chiP_succ_sub_eq]
  have h1 : 0 ≤ ∑ a ∈ Finset.Nat.antidiagonalTuple (D + 1) n,
      -Real.log ((a 0 + 1 : ℝ) / ((n : ℝ) + D + 1)) :=
    Finset.sum_nonneg fun a ha => (chiPAux_neg_log_step_mem D n a ha).1
  have h2 : 0 ≤ ∑ b ∈ (Finset.Nat.antidiagonalTuple (D + 1) (n + 1)).filter (fun b => b 0 = 0),
      -Real.log (monoNormSq b) :=
    Finset.sum_nonneg fun b _ => chiPAux_neg_log_monoNormSq_nonneg b
  linarith
end ReciprocityTheory.GeometryOfNumbersTheory
