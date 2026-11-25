-- Prove2me | solution 1 for ReciprocityTheory.GeometryOfNumbersTheory.chiP_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:20:29.16162+00:00
-- url     : https://prove2.me/submissions/22cece3a-a531-484f-ac41-ec0c7f92498f

import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_SphericalMonomials_MonoNormSq
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_SphericalMonomials_ChiPSt
import Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_monoNormSq_pos
import Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_monoNormSq_le_one

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
theorem _root_.solution (D n : ℕ) : 0 ≤ chiP D n := by
  unfold chiP
  have h : ∑ a ∈ Finset.Nat.antidiagonalTuple (D + 1) n, Real.log (monoNormSq a) ≤ 0 :=
    Finset.sum_nonpos fun a _ => Real.log_nonpos (monoNormSq_pos a).le (monoNormSq_le_one a)
  linarith
end ReciprocityTheory.GeometryOfNumbersTheory
