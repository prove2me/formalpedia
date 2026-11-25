-- Prove2me | solution 1 for ReciprocityTheory.GeometryOfNumbersTheory.chiPAux_filter_zero_eq_empty
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:01:25.444046+00:00
-- url     : https://prove2.me/submissions/5483dbce-383d-4258-ae72-809e2e7f7a6f

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
theorem _root_.solution (n : ℕ) :
    (Finset.Nat.antidiagonalTuple (0 + 1) (n + 1)).filter (fun b => b 0 = 0) = ∅ := by
  rw [Finset.filter_eq_empty_iff]
  intro b hb h0
  have h1 := Finset.Nat.mem_antidiagonalTuple.mp hb
  simp [Fin.sum_univ_succ, h0] at h1 <;> omega
end ReciprocityTheory.GeometryOfNumbersTheory
