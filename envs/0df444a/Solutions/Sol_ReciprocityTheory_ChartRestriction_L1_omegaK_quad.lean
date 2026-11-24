-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.omegaK_quad
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:29:07.047382+00:00
-- url     : https://prove2.me/submissions/8fffd6dd-5a98-41e5-9e03-de5bf884a428

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_CoeffOneSubstOfConstantCoeffEqZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution (d : ℕ) (hd : d % 4 = 3) :
    omegaK d ^ 2 - omegaK d + (((d + 1) / 4 : ℕ) : ℂ) = 0 := by
  unfold omegaK
  have h4 : (((d + 1) / 4 : ℕ) : ℂ) = ((d : ℂ) + 1) / 4 := by
    have h : 4 ∣ d + 1 := by omega
    rw [Nat.cast_div h (by norm_num)]
    push_cast
    ring
  have hs : ((Real.sqrt (d : ℝ) : ℝ) : ℂ) ^ 2 = (d : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
    norm_cast
  rw [h4]
  linear_combination (((Real.sqrt (d : ℝ) : ℝ) : ℂ) ^ 2 / 4) * Complex.I_sq - (1 / 4 : ℂ) * hs
end ReciprocityTheory.ChartRestriction.L1
