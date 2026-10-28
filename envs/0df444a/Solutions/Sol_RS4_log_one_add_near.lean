-- Prove2me | solution 1 for RS4.log_one_add_near
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T05:43:11.169951+00:00
-- url     : https://prove2.me/submissions/2beb60d7-53d5-4169-9bed-11fea2cb2801

import Definitions.Def_ArdaRH65K_Probes_ArbEconomics_Sound
import Definitions.Def_ArdaRH65K_RS4_Sound
import Definitions.Def_ArdaRH65K_RS_B2
import Definitions.Def_ArdaRH65K_RS_B3
import Definitions.Def_ArdaRH65K_RS_C0
import Definitions.Def_ArdaRH65K_RS_Entire
import Definitions.Def_ArdaRH65K_RS_Fold
import Definitions.Def_ArdaRH65K_RS_Kernel
import Definitions.Def_ArdaRH65K_RS_Mellin
import Definitions.Def_ArdaRH65K_RS_Strip
import Definitions.Def_ArdaRS_Arithmetic
import Definitions.Def_ArdaRS_Dyadic
import Definitions.Def_ArdaRS_DyadicOps
import Definitions.Def_ArdaRS_Evaluator
import Mathlib
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic
import Mathlib.Tactic.IntervalCases
namespace ArbEcon
end ArbEcon
namespace DIntvProd
end DIntvProd
namespace DIntvProd.DIntv
end DIntvProd.DIntv

/-  RS4_Sound.lean -- lane B4: SOUNDNESS of the Riemann-Siegel main-term checker `RS4.check`.

    ## The headline

      `RS4.check_sound` : for an evaluator configuration `c` valid at height `t`
      (`ArbEcon.Valid c t K`, i.e. `t = tn / 2^tq` and the pi / Horner / log-kernel facts) and any
      certificate `z`, if the KERNEL accepts (`check c z = true`) then
        * `10000 <= t`, `rsNn t = z.N`, `0 < rsFrac t`, `cos (2 pi rsFrac t) ≠ 0`, and
        * for EVERY phase `phi` with `|phi - rsThetaMain t| <= 1/t`,
              z.zlo / 2^(2P) <= Zmain t phi <= z.zhi / 2^(2P),
          where `Zmain t phi = 2 sum_{n <= N} n^(-1/2) cos(phi - t log n)
                                + (-1)^(N+1) (t/2pi)^(-1/4) rsPsi (rsFrac t)`
          is VERBATIM the main term of `RSInt.rs_Z_C0`.

    The hypotheses of `rs_Z_C0` (`t >= 10000`, `0 < p`, `cos 2 pi p ≠ 0`) are OUTPUTS of the checker,
    so `RS4_Z` combines the two into a hypothesis-free enclosure of Hardy's Z.

    conjecture1_proved = False.  Finite interval arithmetic at one height; nothing about RH.
-/




open Real Finset
open ArbEcon DIntvProd

section
namespace RS4
end RS4
open RS4

noncomputable section



/-! ## 0. small real facts -/



theorem solution {y : ℝ} (h0 : 0 ≤ y) (h1 : y ≤ 1 / 2) :
    |Real.log (1 + y) - Lser y| ≤ 2 * y ^ 9 := by
  have hy : |(-y)| < 1 := by rw [abs_neg, abs_of_nonneg h0]; linarith
  have h := Real.abs_log_sub_add_sum_range_le hy 8
  have hs : (∑ i ∈ Finset.range 8, (-y) ^ (i + 1) / ((i : ℝ) + 1)) = -Lser y := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Lser]; push_cast; ring
  rw [hs, sub_neg_eq_add, abs_neg, abs_of_nonneg h0] at h
  rw [show Real.log (1 + y) - Lser y = -Lser y + Real.log (1 + y) by ring]
  refine le_trans h ?_
  have hpos : 0 < 1 - y := by linarith
  rw [div_le_iff₀ hpos]
  have : 0 ≤ y ^ 9 := by positivity
  rw [show (8 : ℕ) + 1 = 9 from rfl]
  nlinarith [mul_nonneg this (by linarith : (0 : ℝ) ≤ 1 / 2 - y)]
