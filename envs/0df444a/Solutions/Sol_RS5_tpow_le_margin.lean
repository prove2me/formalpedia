-- Prove2me | solution 1 for RS5.tpow_le_margin
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T05:46:08.877174+00:00
-- url     : https://prove2.me/submissions/0f994234-eabe-456c-b107-124c0db9d878

import Definitions.Def_ArdaRH65K_DlvpTheta
import Definitions.Def_ArdaRH65K_Probes_ArbEconomics_Sound
import Definitions.Def_ArdaRH65K_RS4_Sound
import Definitions.Def_ArdaRH65K_RS5_Sound
import Definitions.Def_ArdaRH65K_RS5_Z
import Definitions.Def_ArdaRH65K_RSTheta
import Definitions.Def_ArdaRH65K_RS_B2
import Definitions.Def_ArdaRH65K_RS_B3
import Definitions.Def_ArdaRH65K_RS_C0
import Definitions.Def_ArdaRH65K_RS_Entire
import Definitions.Def_ArdaRH65K_RS_Fold
import Definitions.Def_ArdaRH65K_RS_Kernel
import Definitions.Def_ArdaRH65K_RS_Mellin
import Definitions.Def_ArdaRH65K_RS_Strip
import Definitions.Def_ArdaRH65K_ThetaConverge
import Definitions.Def_ArdaRH65K_ThetaValue
import Definitions.Def_ArdaRH65K_XiLineZeros
import Definitions.Def_ArdaRS_Arithmetic
import Definitions.Def_ArdaRS_Band
import Definitions.Def_ArdaRS_Config64
import Definitions.Def_ArdaRS_Dyadic
import Definitions.Def_ArdaRS_DyadicOps
import Definitions.Def_ArdaRS_Evaluator
import Mathlib
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Tactic
import Mathlib.Tactic.IntervalCases
namespace ArbEcon
end ArbEcon
namespace DIntvProd
end DIntvProd
namespace DIntvProd.DIntv
end DIntvProd.DIntv
namespace RS4
end RS4
namespace RS4.Cert
end RS4.Cert
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

namespace RS4

noncomputable section



/-! ## 0. small real facts -/

















/-! ## 1. the checker's facts, over the reals -/

section Facts

variable {c : Cfg} {t : ℝ} {K : ℕ} {z : Cert}

theorem oneR (hv : Valid c t K) : (c.one : ℝ) = 2 ^ c.P := by
  rw [hv.one_eq]; push_cast; ring





















































/-! ## 2. the Dirichlet state: `psum t N` and `log N` -/







/-! ## 3. the phase ball -/











/-! ## 4. the C0 amplitude `(t/2pi)^(-1/4) = a^(-1/2)` -/









/-! ## 5. the angles `2 pi p` and `2 pi (p - p^2 + 1/16)` -/















end Facts

/-! ## 6. the quotient `Psi = cos v / cos 2 pi p` (denominator bounded away from 0) -/







/-! ## 7. the main sum as `Re (e^{i phi} psum t N)` -/



/-! ## 8. the DIntv assembly -/

section Assembly

variable {c : Cfg} {t : ℝ} {K : ℕ} {z : Cert}









end Assembly

/-! ## 9. THE SOUNDNESS THEOREM -/



end

end RS4


/-  RS5_Z.lean -- lane B5: the t >= 509 checker `RS5.check5` glued to the SEAM bound
    `RSSeam.rs_Z_C0_seam` (remainder (13/5) t^(-3/4)), and certified signs of one dyadic sample.

    ## Headlines (no `sorry`, no `native_decide`, no new axioms)

      * `rs5_Z_enclosure` : `Valid c t K`, `check5 c z = true` give `M > 0`, `phi` with
            Gammaℝ(1/2+it) = M e^{i phi},  |phi - thetaMain t| <= 1/t,
            zlo/2^(2P) - (13/5) t^(-3/4) <= Re completedRiemannZeta(1/2+it) / M
                                         <= zhi/2^(2P) + (13/5) t^(-3/4)
        (the EXACT t-dependent margin of the seam bound; valid from t >= 509).
      * `tpow_le_margin` : `MarginOK c E` (an integer inequality) gives `t^(-3/4) <= E / 2^P`.
      * `rs5_Z_enclosure_E` : the same enclosure with the rational margin `(13/5) E / 2^P`.
      * `rs5_sign_pos` / `rs5_sign_neg` : a box clearing `(13/5) E / 2^P` on one side pins the SIGN of
        `Re completedRiemannZeta(1/2+it)` (= `XiLineZeros.gLine t`).
      * `sampleOK_sign` : a certified `Sample` (`sampleOK s = true`) has the claimed sign of `gLine`
        at `s.t = tn / 2^tq`.

    conjecture1_proved = False.  Finite-height sign certification; nothing about RH.
-/





open Complex
open scoped Real

section
namespace RS5
end RS5
open RS5

open ArbEcon
open RS4 (Cert Zmain)

noncomputable section




theorem solution {c : Cfg} {t : ℝ} {K : ℕ} {E : ℕ} (hv : Valid c t K) (ht : 0 < t)
    (hm : MarginOK c E) : t ^ (-(3 / 4 : ℝ)) ≤ (E : ℝ) / 2 ^ c.P := by
  have hP : (0 : ℝ) < 2 ^ c.P := by positivity
  have hQ : (0 : ℝ) < 2 ^ c.tq := by positivity
  have hm' : ((c.one ^ 4 * (2 ^ c.tq) ^ 3 : ℕ) : ℝ) ≤ ((E ^ 4 * c.tn ^ 3 : ℕ) : ℝ) := by
    exact_mod_cast hm
  push_cast at hm'
  rw [RS4.oneR hv] at hm'
  have htn : (c.tn : ℝ) = t * 2 ^ c.tq := by
    rw [hv.t_eq]; field_simp
  rw [htn] at hm'
  -- hm' : (2^P)^4 (2^tq)^3 <= E^4 (t 2^tq)^3, i.e. 1 <= (E/2^P)^4 t^3
  have key : 1 ≤ ((E : ℝ) / 2 ^ c.P) ^ 4 * t ^ 3 := by
    rw [div_pow, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    have : ((2 : ℝ) ^ c.P) ^ 4 * (2 ^ c.tq) ^ 3 ≤ (E : ℝ) ^ 4 * t ^ 3 * (2 ^ c.tq) ^ 3 := by
      rw [mul_pow] at hm'; linarith
    nlinarith [pow_pos hQ 3]
  set x := t ^ (-(3 / 4 : ℝ)) with hx
  have hx0 : 0 < x := Real.rpow_pos_of_pos ht _
  have hx4 : x ^ 4 * t ^ 3 = 1 := by
    rw [hx, ← Real.rpow_natCast, ← Real.rpow_mul ht.le]
    norm_num
    exact inv_mul_cancel₀ (by positivity)
  by_contra hlt
  push Not at hlt
  have hE0 : (0 : ℝ) ≤ (E : ℝ) / 2 ^ c.P := by positivity
  have h4 : ((E : ℝ) / 2 ^ c.P) ^ 4 < x ^ 4 := pow_lt_pow_left₀ hlt hE0 (by norm_num)
  have ht3 : 0 < t ^ 3 := by positivity
  nlinarith [mul_lt_mul_of_pos_right h4 ht3]
