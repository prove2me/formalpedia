-- Prove2me | solution 1 for ZetaZeros.D.EllReg.one_add_pow_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:06:53.286352+00:00
-- url     : https://prove2.me/submissions/36b2044c-9254-4ef3-ae9c-1012c8e0ef89

import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegCut
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllipticRegularity_KernDecay

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ZetaZeros ZetaZeros.D ZetaZeros.D.EllReg
open MeasureTheory Metric Filter Topology
open scoped ContDiff FourierTransform ENNReal
noncomputable section
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
namespace ZetaZeros.D.EllReg
theorem _root_.solution (t : ℝ) (ht : 0 ≤ t) (n : ℕ) : (1 + t) ^ n ≤ 2 ^ n * (1 + t ^ n) := by
  have htn : 0 ≤ t ^ n := pow_nonneg ht n
  have h2 : (0 : ℝ) ≤ 2 ^ n := by positivity
  rcases le_total t 1 with h | h
  · have h1 : (1 + t) ^ n ≤ 2 ^ n := pow_le_pow_left₀ (by linarith) (by linarith) n
    have h3 : (2 : ℝ) ^ n ≤ 2 ^ n * (1 + t ^ n) := le_mul_of_one_le_right h2 (by linarith)
    linarith
  · have h1 : (1 + t) ^ n ≤ (2 * t) ^ n := pow_le_pow_left₀ (by linarith) (by linarith) n
    have h3 : (2 : ℝ) ^ n * t ^ n ≤ 2 ^ n * (1 + t ^ n) := mul_le_mul_of_nonneg_left (by linarith) h2
    rw [mul_pow] at h1
    linarith
end ZetaZeros.D.EllReg
