-- Prove2me | solution 1 for RS5.sampleOK_sign
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T06:47:00.168824+00:00
-- url     : https://prove2.me/submissions/106a5c52-88e6-49b6-be76-5d145cb5c910

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
import Theorems.Thm_ArbEcon_OrderK_valid64
import Theorems.Thm_RS5_check5_sound
import Theorems.Thm_RS5_tpow_le_margin
import Theorems.Thm_RSSeam_rs_Z_C0_seam
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

namespace RS5

open ArbEcon
open RS4 (Cert Zmain)

noncomputable section

/-- **Retargeted enclosure (t >= 509), exact margin `(13/5) t^(-3/4)`.** -/
theorem rs5_Z_enclosure {c : Cfg} {t : ℝ} {K : ℕ} (hv : Valid c t K) (z : Cert)
    (h : check5 c z = true) :
    ∃ M φ : ℝ, 0 < M ∧ Gammaℝ ((1 / 2 : ℂ) + t * I) = (M : ℂ) * cexp (I * φ) ∧
      |φ - RSInt.rsThetaMain t| ≤ 1 / t ∧
      (z.zlo : ℝ) / 2 ^ (2 * c.P) - 13 / 5 * t ^ (-(3 / 4 : ℝ)) ≤
        (completedRiemannZeta ((1 / 2 : ℂ) + t * I)).re / M ∧
      (completedRiemannZeta ((1 / 2 : ℂ) + t * I)).re / M ≤
        (z.zhi : ℝ) / 2 ^ (2 * c.P) + 13 / 5 * t ^ (-(3 / 4 : ℝ)) := by
  obtain ⟨ht, _, hp, hcos, hZ⟩ := check5_sound hv z h
  obtain ⟨M, φ, hM, hpol, hφ, hb⟩ := RSSeam.rs_Z_C0_seam ht hp hcos
  refine ⟨M, φ, hM, hpol, hφ, ?_⟩
  have hz := hZ φ hφ
  unfold Zmain at hz
  rw [abs_le] at hb
  constructor <;> linarith [hz.1, hz.2, hb.1, hb.2]



/-- **Retargeted enclosure with the rational margin `(13/5) E / 2^P`.** -/
theorem rs5_Z_enclosure_E {c : Cfg} {t : ℝ} {K : ℕ} (hv : Valid c t K) (z : Cert) {E : ℕ}
    (h : check5 c z = true) (hm : MarginOK c E) :
    ∃ M φ : ℝ, 0 < M ∧ Gammaℝ ((1 / 2 : ℂ) + t * I) = (M : ℂ) * cexp (I * φ) ∧
      |φ - RSInt.rsThetaMain t| ≤ 1 / t ∧
      (z.zlo : ℝ) / 2 ^ (2 * c.P) - 13 / 5 * ((E : ℝ) / 2 ^ c.P) ≤
        (completedRiemannZeta ((1 / 2 : ℂ) + t * I)).re / M ∧
      (completedRiemannZeta ((1 / 2 : ℂ) + t * I)).re / M ≤
        (z.zhi : ℝ) / 2 ^ (2 * c.P) + 13 / 5 * ((E : ℝ) / 2 ^ c.P) := by
  obtain ⟨M, φ, hM, hpol, hφ, h1, h2⟩ := rs5_Z_enclosure hv z h
  have ht : (509 : ℝ) ≤ t := (check5_sound hv z h).1
  have hmr := tpow_le_margin hv (by linarith) hm
  exact ⟨M, φ, hM, hpol, hφ, by linarith, by linarith⟩

theorem posOK_real {c : Cfg} {t : ℝ} {K : ℕ} (hv : Valid c t K) {z : Cert} {E : ℕ}
    (hp : PosOK c z E) : 13 / 5 * ((E : ℝ) / 2 ^ c.P) < (z.zlo : ℝ) / 2 ^ (2 * c.P) := by
  have hP : (0 : ℝ) < 2 ^ c.P := by positivity
  have h : ((13 * (E : ℤ) * (c.one : ℤ) : ℤ) : ℝ) < ((5 * z.zlo : ℤ) : ℝ) := by exact_mod_cast hp
  push_cast at h
  rw [RS4.oneR hv] at h
  have e : (z.zlo : ℝ) / 2 ^ (2 * c.P) - 13 / 5 * ((E : ℝ) / 2 ^ c.P)
      = (5 * z.zlo - 13 * E * 2 ^ c.P) / (5 * (2 ^ c.P) ^ 2) := by
    rw [pow_mul']; field_simp
  have : 0 < (5 * (z.zlo : ℝ) - 13 * E * 2 ^ c.P) / (5 * (2 ^ c.P) ^ 2) :=
    div_pos (by linarith) (by positivity)
  linarith

theorem negOK_real {c : Cfg} {t : ℝ} {K : ℕ} (hv : Valid c t K) {z : Cert} {E : ℕ}
    (hn : NegOK c z E) : (z.zhi : ℝ) / 2 ^ (2 * c.P) < -(13 / 5 * ((E : ℝ) / 2 ^ c.P)) := by
  have hP : (0 : ℝ) < 2 ^ c.P := by positivity
  have h : ((5 * z.zhi : ℤ) : ℝ) < ((-(13 * (E : ℤ) * (c.one : ℤ)) : ℤ) : ℝ) := by exact_mod_cast hn
  push_cast at h
  rw [RS4.oneR hv] at h
  have e : -(13 / 5 * ((E : ℝ) / 2 ^ c.P)) - (z.zhi : ℝ) / 2 ^ (2 * c.P)
      = (-(13 * E * 2 ^ c.P) - 5 * z.zhi) / (5 * (2 ^ c.P) ^ 2) := by
    rw [pow_mul']; field_simp
  have : 0 < (-(13 * (E : ℝ) * 2 ^ c.P) - 5 * z.zhi) / (5 * (2 ^ c.P) ^ 2) :=
    div_pos (by linarith) (by positivity)
  linarith

/-- A certified box above `(13/5) E / 2^P` gives `Re completedRiemannZeta(1/2+it) > 0`. -/
theorem rs5_sign_pos {c : Cfg} {t : ℝ} {K : ℕ} (hv : Valid c t K) (z : Cert) {E : ℕ}
    (h : check5 c z = true) (hm : MarginOK c E) (hpos : PosOK c z E) :
    0 < (completedRiemannZeta ((1 / 2 : ℂ) + t * I)).re := by
  obtain ⟨M, _, hM, _, _, h1, _⟩ := rs5_Z_enclosure_E hv z h hm
  have := posOK_real hv hpos
  have : 0 < (completedRiemannZeta ((1 / 2 : ℂ) + t * I)).re / M := by linarith
  exact (div_pos_iff_of_pos_right hM).mp this

/-- A certified box below `-(13/5) E / 2^P` gives `Re completedRiemannZeta(1/2+it) < 0`. -/
theorem rs5_sign_neg {c : Cfg} {t : ℝ} {K : ℕ} (hv : Valid c t K) (z : Cert) {E : ℕ}
    (h : check5 c z = true) (hm : MarginOK c E) (hneg : NegOK c z E) :
    (completedRiemannZeta ((1 / 2 : ℂ) + t * I)).re < 0 := by
  obtain ⟨M, _, hM, _, _, _, h2⟩ := rs5_Z_enclosure_E hv z h hm
  have := negOK_real hv hneg
  have : (completedRiemannZeta ((1 / 2 : ℂ) + t * I)).re / M < 0 := by linarith
  by_contra hc
  have := div_nonneg (not_lt.mp hc) hM.le
  linarith

/-! ## one sample -/



theorem Sample.valid (s : Sample) : Valid s.cfg s.t 9 := ArbEcon.OrderK.valid64 s.tn s.tq _ rfl



end

end RS5


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















/-! ## one sample -/






theorem solution {s : Sample} (h : sampleOK s = true) :
    (s.pos = true → 0 < XiLineZeros.gLine s.t) ∧ (s.pos = false → XiLineZeros.gLine s.t < 0) := by
  unfold sampleOK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hc, hm⟩, hs⟩ := h
  constructor
  · intro hp
    rw [hp, if_pos rfl, decide_eq_true_eq] at hs
    exact rs5_sign_pos s.valid s.z hc hm hs
  · intro hp
    rw [hp] at hs
    simp only [Bool.false_eq_true, if_false, decide_eq_true_eq] at hs
    exact rs5_sign_neg s.valid s.z hc hm hs
