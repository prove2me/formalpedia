-- Prove2me | solution 1 for ReciprocityTheory.GeometryOfNumbersTheory.chiPAux_sum_update_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:21:43.811805+00:00
-- url     : https://prove2.me/submissions/96382390-bfcf-4198-813b-3aeaa429f9d5

import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_SphericalMonomials_MonoNormSq
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_SphericalMonomials_ChiPSt

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
theorem _root_.solution {D : ℕ} (a : Fin (D + 1) → ℕ) (v : ℕ) :
    ∑ i, Function.update a 0 v i = v + ∑ i : Fin D, a i.succ := by
  rw [Fin.sum_univ_succ]
  simp [Function.update_apply, Fin.succ_ne_zero]
end ReciprocityTheory.GeometryOfNumbersTheory
