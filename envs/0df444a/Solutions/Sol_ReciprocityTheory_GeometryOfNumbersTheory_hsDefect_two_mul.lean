-- Prove2me | solution 1 for ReciprocityTheory.GeometryOfNumbersTheory.hsDefect_two_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:01:38.983279+00:00
-- url     : https://prove2.me/submissions/bd404f03-5766-4a41-9aab-6fa423c85e1e

import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_AsymptoticSequences_DefectSt
import Mathlib
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_AsymptoticSequences_ClosingHS

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.GeometryOfNumbersTheory
open Filter Topology Asymptotics
namespace ReciprocityTheory.GeometryOfNumbersTheory
theorem _root_.solution (D : ℕ) (hh : ℝ) (n : ℕ) :
    hsDefect D (fun m => chiP D (2 * m)) (2 ^ (D + 1) * hh) n = hsDefect D (chiP D) hh (2 * n) := by
  unfold hsDefect
  push_cast
  rw [mul_pow]
  ring
end ReciprocityTheory.GeometryOfNumbersTheory
