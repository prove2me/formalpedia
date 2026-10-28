-- Prove2me | solution 1 for RS5.lg_lo
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T05:46:21.080724+00:00
-- url     : https://prove2.me/submissions/2a231f30-f13f-4d7b-89cb-09c097ca8061

import Definitions.Def_ArdaRH65K_Probes_ArbEconomics_Sound
import Definitions.Def_ArdaRH65K_RS4_Sound
import Definitions.Def_ArdaRH65K_RS5_Sound
import Definitions.Def_ArdaRH65K_RS_B2
import Definitions.Def_ArdaRH65K_RS_B3
import Definitions.Def_ArdaRH65K_RS_C0
import Definitions.Def_ArdaRH65K_RS_Entire
import Definitions.Def_ArdaRH65K_RS_Fold
import Definitions.Def_ArdaRH65K_RS_Kernel
import Definitions.Def_ArdaRH65K_RS_Mellin
import Definitions.Def_ArdaRH65K_RS_Strip
import Definitions.Def_ArdaRS_Arithmetic
import Definitions.Def_ArdaRS_Band
import Definitions.Def_ArdaRS_Config64
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
import Theorems.Thm_RS4_log_one_add_near
namespace ArbEcon
end ArbEcon
namespace ArbEcon.Trig
end ArbEcon.Trig
namespace ArbEcon.sgn
end ArbEcon.sgn
namespace DIntvProd
end DIntvProd
namespace DIntvProd.DIntv
end DIntvProd.DIntv
namespace RS4
end RS4
namespace RS4.Cert
end RS4.Cert
namespace RS4.Lser
end RS4.Lser
namespace RS4.negIf
end RS4.negIf
namespace RS4.sgnI
end RS4.sgnI
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





theorem lp_real (Y o : ℕ) (ho : 0 < o) :
    ((lpPos Y o : ℕ) : ℝ) - (lpNeg Y o : ℕ) = 840 * (o : ℝ) ^ 9 * Lser ((Y : ℝ) / o) := by
  have hoR : (o : ℝ) ≠ 0 := by exact_mod_cast ho.ne'
  unfold lpPos lpNeg Lser
  push_cast
  field_simp
  ring











/-! ## 1. the checker's facts, over the reals -/

section Facts

variable {c : Cfg} {t : ℝ} {K : ℕ} {z : Cert}























































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


/-  RS5_Sound.lean -- lane B5: SOUNDNESS of the t >= 509 checker `RS5.check5`.

    This file is lane B4's `RS4_Sound` sections 1-9 (the checker's facts over the reals, the DIntv
    assembly and the soundness theorem) re-stated for `RS5.Checks5`, which differs from `RS4.Checks`
    ONLY in the height floor (`509 * 2^tq <= tn` instead of `10000 * 2^tq <= tn`).  The floor is used by
    exactly two facts, `t_ge` and `tn_pos`; every other proof is unchanged text.  The height-free
    helpers of `RS4_Sound` (`Zmain`, `Lser`, `log_one_add_near`, `lp_real`, `ballD_mem`, ...) and all
    computable definitions of `RS4_Eval` are REUSED (selective `open RS4 (...)`), not duplicated.

    ## The headline

      `RS5.check5_sound` : `Valid c t K` and `check5 c z = true` imply
        `509 <= t`, `rsNn t = z.N`, `0 < rsFrac t`, `cos (2 pi rsFrac t) ≠ 0`, and for EVERY phase
        `phi` with `|phi - rsThetaMain t| <= 1/t`:  `zlo / 2^(2P) <= RS4.Zmain t phi <= zhi / 2^(2P)`.

    conjecture1_proved = False.  Finite interval arithmetic at one height; nothing about RH.
-/



open Real Finset
open ArbEcon DIntvProd
open RS4 (Cert lpPos lpNeg sgnI ballD negIf dstate phTrig mainBox c0Box zBox QuotOK Zmain Lser
  log_one_add_near lp_real     )

namespace RS5

noncomputable section

/-! ## 1. the checker's facts, over the reals -/

section Facts

variable {c : Cfg} {t : ℝ} {K : ℕ} {z : Cert}

theorem oneR (hv : Valid c t K) : (c.one : ℝ) = 2 ^ c.P := by
  rw [hv.one_eq]; push_cast; ring

theorem pi_lo (hv : Valid c t K) : (c.hp : ℝ) - c.rp ≤ π / 2 * 2 ^ c.P := by
  have := hv.pi_ball; rw [abs_le] at this; linarith [this.1]

theorem pi_hi (hv : Valid c t K) : π / 2 * 2 ^ c.P ≤ (c.hp : ℝ) + c.rp := by
  have := hv.pi_ball; rw [abs_le] at this; linarith [this.2]

theorem t_ge (hv : Valid c t K) (hk : Checks5 c z) : 509 ≤ t := by
  rw [hv.t_eq, le_div_iff₀ (by positivity)]
  have := hk.ht
  exact_mod_cast this

theorem t_pos (hv : Valid c t K) (hk : Checks5 c z) : 0 < t := by
  linarith [t_ge hv hk]

/-- `a = rsAlpha t` squared. -/
theorem alpha_sq (ht : 0 < t) : RSInt.rsAlpha t ^ 2 = t / (2 * π) :=
  Real.sq_sqrt (by positivity)

theorem alpha_nonneg (t : ℝ) : 0 ≤ RSInt.rsAlpha t := Real.sqrt_nonneg _

/-- `(a 2^P)^2 * (2^tq * 4 * (pi/2 * 2^P)) = tn * 2^(3P)`. -/
theorem alpha_key (hv : Valid c t K) (hk : Checks5 c z) :
    (RSInt.rsAlpha t * 2 ^ c.P) ^ 2 * (2 ^ c.tq * 4 * (π / 2 * 2 ^ c.P)) =
      (c.tn : ℝ) * (2 ^ c.P * 2 ^ c.P * 2 ^ c.P) := by
  have ht := t_pos hv hk
  have hq : (0 : ℝ) < 2 ^ c.tq := by positivity
  rw [mul_pow, alpha_sq ht, hv.t_eq]
  field_simp
  ring

theorem A0_le (hv : Valid c t K) (hk : Checks5 c z) :
    (z.A0 : ℝ) ≤ RSInt.rsAlpha t * 2 ^ c.P := by
  have hP : (0 : ℝ) < 2 ^ c.P := by positivity
  have hq : (0 : ℝ) < 2 ^ c.tq := by positivity
  have h := hk.hA0
  have hR : ((z.A0 * z.A0 * 2 ^ c.tq * 4 * (c.hp + c.rp) : ℕ) : ℝ)
      ≤ ((c.tn * (c.one * c.one * c.one) : ℕ) : ℝ) := by exact_mod_cast h
  push_cast at hR
  rw [oneR hv] at hR
  have key := alpha_key hv hk
  have hpi := pi_hi hv
  have hx := mul_nonneg (alpha_nonneg t) hP.le
  by_contra hcon
  rw [not_le] at hcon
  have hsq : (RSInt.rsAlpha t * 2 ^ c.P) ^ 2 < (z.A0 : ℝ) ^ 2 := by
    apply pow_lt_pow_left₀ hcon hx (by norm_num)
  have hw : (0 : ℝ) < 2 ^ c.tq * 4 * (π / 2 * 2 ^ c.P) := by positivity
  have h1 : (RSInt.rsAlpha t * 2 ^ c.P) ^ 2 * (2 ^ c.tq * 4 * (π / 2 * 2 ^ c.P))
      < (z.A0 : ℝ) ^ 2 * (2 ^ c.tq * 4 * (π / 2 * 2 ^ c.P)) := mul_lt_mul_of_pos_right hsq hw
  have h2 : (z.A0 : ℝ) ^ 2 * (2 ^ c.tq * 4 * (π / 2 * 2 ^ c.P))
      ≤ (z.A0 : ℝ) ^ 2 * (2 ^ c.tq * 4 * ((c.hp : ℝ) + c.rp)) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply mul_le_mul_of_nonneg_left hpi (by positivity)
  nlinarith

theorem A1_ge (hv : Valid c t K) (hk : Checks5 c z) :
    RSInt.rsAlpha t * 2 ^ c.P ≤ (z.A1 : ℝ) := by
  have hP : (0 : ℝ) < 2 ^ c.P := by positivity
  have h := hk.hA1
  have hR : ((c.tn * (c.one * c.one * c.one) : ℕ) : ℝ)
      ≤ ((z.A1 * z.A1 * 2 ^ c.tq * 4 * (c.hp - c.rp) : ℕ) : ℝ) := by exact_mod_cast h
  push_cast [Nat.cast_sub hk.hrp] at hR
  rw [oneR hv] at hR
  have key := alpha_key hv hk
  have hpi := pi_lo hv
  have hx := mul_nonneg (alpha_nonneg t) hP.le
  by_contra hcon
  rw [not_le] at hcon
  have hsq : (z.A1 : ℝ) ^ 2 < (RSInt.rsAlpha t * 2 ^ c.P) ^ 2 := by
    apply pow_lt_pow_left₀ hcon (by positivity) (by norm_num)
  have hpipos : (0 : ℝ) < π / 2 * 2 ^ c.P := by positivity
  have h2 : (z.A1 : ℝ) ^ 2 * (2 ^ c.tq * 4 * ((c.hp : ℝ) - c.rp))
      ≤ (z.A1 : ℝ) ^ 2 * (2 ^ c.tq * 4 * (π / 2 * 2 ^ c.P)) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply mul_le_mul_of_nonneg_left hpi (by positivity)
  have hw : (0 : ℝ) < 2 ^ c.tq * 4 * (π / 2 * 2 ^ c.P) := by positivity
  have h1 : (z.A1 : ℝ) ^ 2 * (2 ^ c.tq * 4 * (π / 2 * 2 ^ c.P))
      < (RSInt.rsAlpha t * 2 ^ c.P) ^ 2 * (2 ^ c.tq * 4 * (π / 2 * 2 ^ c.P)) :=
    mul_lt_mul_of_pos_right hsq hw
  nlinarith

theorem N_lt_alpha (hv : Valid c t K) (hk : Checks5 c z) : (z.N : ℝ) < RSInt.rsAlpha t := by
  have hP : (0 : ℝ) < 2 ^ c.P := by positivity
  have h : ((z.N * c.one : ℕ) : ℝ) < (z.A0 : ℝ) := by exact_mod_cast hk.hNlo
  push_cast at h; rw [oneR hv] at h
  have := A0_le hv hk
  by_contra hc; rw [not_lt] at hc
  nlinarith

theorem alpha_lt_N1 (hv : Valid c t K) (hk : Checks5 c z) : RSInt.rsAlpha t < (z.N : ℝ) + 1 := by
  have hP : (0 : ℝ) < 2 ^ c.P := by positivity
  have h : (z.A1 : ℝ) < (((z.N + 1) * c.one : ℕ) : ℝ) := by exact_mod_cast hk.hNhi
  push_cast at h; rw [oneR hv] at h
  have := A1_ge hv hk
  by_contra hc; rw [not_lt] at hc
  nlinarith

theorem N_eq (hv : Valid c t K) (hk : Checks5 c z) : RSInt.rsNn t = z.N := by
  unfold RSInt.rsNn
  rw [Nat.floor_eq_iff (alpha_nonneg t)]
  exact ⟨(N_lt_alpha hv hk).le, alpha_lt_N1 hv hk⟩

theorem frac_eq (hv : Valid c t K) (hk : Checks5 c z) :
    RSInt.rsFrac t = RSInt.rsAlpha t - z.N := by
  unfold RSInt.rsFrac; rw [N_eq hv hk]



theorem NO_le_A0 (hk : Checks5 c z) : z.N * c.one ≤ z.A0 := le_of_lt hk.hNlo

theorem NO_le_A1 (hv : Valid c t K) (hk : Checks5 c z) : z.N * c.one ≤ z.A1 := by
  have h1 : ((z.N * c.one : ℕ) : ℝ) < z.A0 := by exact_mod_cast hk.hNlo
  have h2 := A0_le hv hk
  have h3 := A1_ge hv hk
  have : ((z.N * c.one : ℕ) : ℝ) ≤ z.A1 := by linarith
  exact_mod_cast this

/-- `p 2^P` lies in `[A0 - N o, A1 - N o]`. -/
theorem p_lo (hv : Valid c t K) (hk : Checks5 c z) :
    (((z.A0 - z.N * c.one : ℕ)) : ℝ) ≤ RSInt.rsFrac t * 2 ^ c.P := by
  rw [Nat.cast_sub (NO_le_A0 hk), frac_eq hv hk]
  push_cast; rw [oneR hv]
  have := A0_le hv hk
  nlinarith

theorem p_hi (hv : Valid c t K) (hk : Checks5 c z) :
    RSInt.rsFrac t * 2 ^ c.P ≤ (((z.A1 - z.N * c.one : ℕ)) : ℝ) := by
  rw [Nat.cast_sub (NO_le_A1 hv hk), frac_eq hv hk]
  push_cast; rw [oneR hv]
  have := A1_ge hv hk
  nlinarith

theorem N_pos (hk : Checks5 c z) : (0 : ℝ) < z.N := by
  have := hk.hN; exact_mod_cast this

/-- `y = p / N` bracket. -/
theorem y_lo (hv : Valid c t K) (hk : Checks5 c z) :
    (z.Y0 : ℝ) ≤ RSInt.rsFrac t / z.N * 2 ^ c.P := by
  have hN := N_pos hk
  have h : ((z.Y0 * z.N : ℕ) : ℝ) ≤ ((z.A0 - z.N * c.one : ℕ) : ℝ) := by exact_mod_cast hk.hY0
  have hp := p_lo hv hk
  push_cast at h
  rw [div_mul_eq_mul_div, le_div_iff₀ hN]
  linarith

theorem y_hi (hv : Valid c t K) (hk : Checks5 c z) :
    RSInt.rsFrac t / z.N * 2 ^ c.P ≤ (z.Y1 : ℝ) := by
  have hN := N_pos hk
  have h : ((z.A1 - z.N * c.one : ℕ) : ℝ) ≤ ((z.Y1 * z.N : ℕ) : ℝ) := by exact_mod_cast hk.hY1
  have hp := p_hi hv hk
  push_cast at h
  rw [div_mul_eq_mul_div, div_le_iff₀ hN]
  linarith



theorem y_le_half (hv : Valid c t K) (hk : Checks5 c z) : RSInt.rsFrac t / z.N ≤ 1 / 2 := by
  have hP : (0 : ℝ) < 2 ^ c.P := by positivity
  have h : ((2 * z.Y1 : ℕ) : ℝ) ≤ (c.one : ℝ) := by exact_mod_cast hk.hYhalf
  push_cast at h; rw [oneR hv] at h
  have := y_hi hv hk
  by_contra hc; rw [not_le] at hc
  nlinarith







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

end RS5


/-  RS5_Sound.lean -- lane B5: SOUNDNESS of the t >= 509 checker `RS5.check5`.

    This file is lane B4's `RS4_Sound` sections 1-9 (the checker's facts over the reals, the DIntv
    assembly and the soundness theorem) re-stated for `RS5.Checks5`, which differs from `RS4.Checks`
    ONLY in the height floor (`509 * 2^tq <= tn` instead of `10000 * 2^tq <= tn`).  The floor is used by
    exactly two facts, `t_ge` and `tn_pos`; every other proof is unchanged text.  The height-free
    helpers of `RS4_Sound` (`Zmain`, `Lser`, `log_one_add_near`, `lp_real`, `ballD_mem`, ...) and all
    computable definitions of `RS4_Eval` are REUSED (selective `open RS4 (...)`), not duplicated.

    ## The headline

      `RS5.check5_sound` : `Valid c t K` and `check5 c z = true` imply
        `509 <= t`, `rsNn t = z.N`, `0 < rsFrac t`, `cos (2 pi rsFrac t) ≠ 0`, and for EVERY phase
        `phi` with `|phi - rsThetaMain t| <= 1/t`:  `zlo / 2^(2P) <= RS4.Zmain t phi <= zhi / 2^(2P)`.

    conjecture1_proved = False.  Finite interval arithmetic at one height; nothing about RH.
-/



open Real Finset
open ArbEcon DIntvProd
open RS4 (Cert lpPos lpNeg sgnI ballD negIf dstate phTrig mainBox c0Box zBox QuotOK Zmain Lser
  log_one_add_near lp_real     )

section
namespace RS5
end RS5
open RS5

noncomputable section

/-! ## 1. the checker's facts, over the reals -/

section Facts

variable {c : Cfg} {t : ℝ} {K : ℕ} {z : Cert}




















































theorem solution (hv : Valid c t K) (hk : Checks5 c z) :
    (z.LG0 : ℝ) ≤ Real.log (1 + RSInt.rsFrac t / z.N) * 2 ^ c.P := by
  have hP : (0 : ℝ) < 2 ^ c.P := by positivity
  have ho : 0 < c.one := by rw [hv.one_eq]; positivity
  set y := RSInt.rsFrac t / z.N with hydef
  set y0 : ℝ := (z.Y0 : ℝ) / 2 ^ c.P with hy0
  have hy0le : y0 ≤ y := by rw [hy0, div_le_iff₀ hP]; exact y_lo hv hk
  have hy00 : 0 ≤ y0 := by positivity
  have hyh := y_le_half hv hk
  have hmono : Real.log (1 + y0) ≤ Real.log (1 + y) :=
    Real.log_le_log (by linarith) (by linarith)
  have hser := log_one_add_near hy00 (by linarith)
  rw [abs_le] at hser
  have h : ((z.LG0 * 840 * c.one ^ 8 + 1680 * z.Y0 ^ 9 + lpNeg z.Y0 c.one : ℕ) : ℝ)
      ≤ ((lpPos z.Y0 c.one : ℕ) : ℝ) := by exact_mod_cast hk.hLG0
  have hl := lp_real z.Y0 c.one ho
  rw [oneR hv] at hl
  push_cast at h
  rw [oneR hv] at h
  -- h : LG0 840 O^8 + 1680 Y0^9 + neg <= pos ; hl : pos - neg = 840 O^9 L(y0)
  have hY : (z.Y0 : ℝ) = y0 * 2 ^ c.P := by rw [hy0]; field_simp
  rw [← hy0] at hl
  have h2 : (z.LG0 : ℝ) * 840 * (2 ^ c.P) ^ 8 + 1680 * (y0 * 2 ^ c.P) ^ 9
      ≤ 840 * (2 ^ c.P) ^ 9 * Lser y0 := by rw [← hY]; linarith
  have h3 : (z.LG0 : ℝ) ≤ (Lser y0 - 2 * y0 ^ 9) * 2 ^ c.P := by
    have hO8 : (0 : ℝ) < 840 * (2 ^ c.P) ^ 8 := by positivity
    rw [← mul_le_mul_iff_left₀ hO8]
    have e : (Lser y0 - 2 * y0 ^ 9) * 2 ^ c.P * (840 * (2 ^ c.P) ^ 8)
        = 840 * (2 ^ c.P) ^ 9 * Lser y0 - 1680 * (y0 * 2 ^ c.P) ^ 9 := by ring
    rw [e]; linarith
  have h4 : (Lser y0 - 2 * y0 ^ 9) * 2 ^ c.P ≤ Real.log (1 + y) * 2 ^ c.P :=
    mul_le_mul_of_nonneg_right (by linarith [hser.2]) hP.le
  linarith
