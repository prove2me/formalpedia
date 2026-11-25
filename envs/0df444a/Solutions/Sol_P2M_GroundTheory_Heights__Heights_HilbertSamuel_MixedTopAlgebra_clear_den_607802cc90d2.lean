-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_MixedTopAlgebra_clear_den_607802cc90d2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:26:33.723801+00:00
-- url     : https://prove2.me/submissions/f07cf704-6ba2-42e2-9eda-eb822ea9700a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsMixedTopAlgebra
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsPolyNonnegAtZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PMixedTopAlgebra

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open Filter Polynomial
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
namespace MixedTopAlgebra
theorem _root_.solution (d : ℕ) (m : ℕ → ℝ) (Q x : ℝ) (hQ : Q ≠ 0) :
    Q ^ d * ∑ i ∈ Finset.range (d + 1), (d.choose i : ℝ) * m i * (x / Q) ^ i =
      ∑ i ∈ Finset.range (d + 1), (d.choose i : ℝ) * Q ^ (d - i) * x ^ i * m i := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hid : i ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have hpow : Q ^ d = Q ^ (d - i) * Q ^ i := by rw [← pow_add, Nat.sub_add_cancel hid]
  rw [hpow, div_pow]
  field_simp
end MixedTopAlgebra
end GroundTheory.Heights₂.Heights.HilbertSamuel
