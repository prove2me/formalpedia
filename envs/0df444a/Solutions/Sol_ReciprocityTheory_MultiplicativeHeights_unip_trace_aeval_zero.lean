-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.unip_trace_aeval_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:26:14.235277+00:00
-- url     : https://prove2.me/submissions/0ef3e6df-a9e4-456b-9ac0-82c1531d5e13

import Mathlib
import Definitions.Def_ReciprocityTheory_SemistableReduction_UnipotentA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open Polynomial Matrix
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution {K : Type*} [Field K] {r : ℕ} (N : Matrix (Fin r) (Fin r) K)
    (hN : ∀ k, 1 ≤ k → k ≤ r → (N ^ k).trace = 0) (P : K[X]) (hP : P.natDegree ≤ r) :
    (aeval N P).trace = P.coeff 0 * r := by
  rw [Polynomial.aeval_eq_sum_range, Matrix.trace_sum, Finset.sum_range_succ', Finset.sum_eq_zero]
  · simp [Matrix.trace_one]
  · intro i hi
    have hi' := Finset.mem_range.mp hi
    rw [Matrix.trace_smul, hN (i + 1) (by omega) (by omega), smul_zero]
end ReciprocityTheory.MultiplicativeHeights
