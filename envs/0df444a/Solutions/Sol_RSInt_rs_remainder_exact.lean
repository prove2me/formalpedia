-- Prove2me | solution 1 for RSInt.rs_remainder_exact
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T06:29:49.516993+00:00
-- url     : https://prove2.me/submissions/69b48ad1-308b-4d54-be87-c9ce06c6a1e6

import Definitions.Def_ArdaRH65K_RS_B2
import Definitions.Def_ArdaRH65K_RS_B3
import Definitions.Def_ArdaRH65K_RS_C0
import Definitions.Def_ArdaRH65K_RS_Entire
import Definitions.Def_ArdaRH65K_RS_Fold
import Definitions.Def_ArdaRH65K_RS_Kernel
import Definitions.Def_ArdaRH65K_RS_Mellin
import Definitions.Def_ArdaRH65K_RS_Strip
import Mathlib
import Theorems.Thm_RSInt_rsJ_C0
import Theorems.Thm_RSInt_rsRem_factor
/-  RS_B3.lean -- lane RS, brick B3 (the explicit Riemann-Siegel remainder), part 2: the exact
    saddle-point reduction.  Mathlib-only (imports `RS_C0`).

    ## Vocabulary (height t > 0)

        a = rsAlpha t = sqrt(t / 2 pi),  N = rsNn t = floor a,  p = rsFrac t = a - N,
        rsThetaMain t = (t/2) log t - (t/2) log(2 pi) - t/2 - pi/8   (verbatim the corpus thetaMain),
        rsPsi p = cos(2 pi (p^2 - p - 1/16)) / cos(2 pi p)            (Gabcke's C0 = Riemann's Psi),
        rsRem t = -lineUp (N + 1/2) (x |-> rsG x x^(-(1/2 + i t)))    (the exact RS remainder, B2).

    By B2 (`completed_re_eq_rs_cos`), on the critical line
        Re completedRiemannZeta(1/2+it) = 2M ( sum_{n<=N} n^(-1/2) cos(phi - t log n) + Re(e^{i phi} rsRem t) ).

    ## What this file proves (no `sorry`, no `native_decide`, no new axioms)

      * `rsRem_factor` : moving the remainder line to the saddle point a and factoring out the
        stationary phase,
            rsRem t = (-1)^(N+1) e^{i pi a^2} a^(-s) (rsJ p + rsE1 a p),
        where rsJ is the tau = 2 Mordell integral (RS_C0) and rsE1 the error integral of the amplitude
        rsPhi a w - 1,  rsPhi a w = e^{2 pi i a w - pi i w^2} (1 + w/a)^(-s).
      * `rs_phase` : e^{i phi} e^{i pi a^2} a^(-s) = a^(-1/2) e^{i (phi - rsThetaMain t - pi/8)}.
      * `rs_remainder_exact` : the EXACT identity
            2 Re(e^{i phi} rsRem t) - (-1)^(N+1) a^(-1/2) Psi(p)
              = (-1)^(N+1) a^(-1/2) [ 2 Re(e^{-i pi/8}(e^{i delta} - 1) rsJ p)
                                      + 2 Re(e^{i (delta - pi/8)} rsE1 a p) ],   delta = phi - thetaMain t,
        so the C0-corrected remainder is controlled by |delta| |rsJ p| and |rsE1 a p| alone.

    conjecture1_proved = False.
-/


open Complex MeasureTheory Filter Topology Set
open scoped Real ComplexConjugate

noncomputable section

namespace RSInt

/-! ## 0. Vocabulary -/

















theorem rsAlpha_pos {t : ℝ} (ht : 0 < t) : 0 < rsAlpha t := Real.sqrt_pos.mpr (by positivity)

theorem rsAlpha_sq {t : ℝ} (ht : 0 ≤ t) : rsAlpha t ^ 2 = t / (2 * π) :=
  Real.sq_sqrt (by positivity)





theorem rsAlpha_lt {t : ℝ} : rsAlpha t < rsNn t + 1 := Nat.lt_floor_add_one _

theorem rsFrac_lt_one {t : ℝ} : rsFrac t < 1 := by
  unfold rsFrac; linarith [rsAlpha_lt (t := t)]



/-! ## 1. Shifting the denominator by an integer -/



/-! ## 2. The factorization at the saddle point -/











/-! ## 3. The phase -/

theorem rs_phase {t : ℝ} (ht : 0 < t) (φ : ℝ) :
    cexp (I * φ) * (cexp (↑π * I * (rsAlpha t) ^ 2) * ((rsAlpha t : ℂ) ^ (-((1 / 2 : ℂ) + t * I)))) =
      (((rsAlpha t) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * cexp (I * (φ - rsThetaMain t - π / 8)) := by
  set a := rsAlpha t with hadef
  have ha : 0 < a := rsAlpha_pos ht
  have ha2 : a ^ 2 = t / (2 * π) := rsAlpha_sq ht.le
  have hlog : Real.log a = (Real.log t - Real.log (2 * π)) / 2 := by
    have h1 : Real.log (a ^ 2) = Real.log t - Real.log (2 * π) := by
      rw [ha2, Real.log_div ht.ne' (by positivity)]
    rw [Real.log_pow] at h1; push_cast at h1; linarith
  have hcpow : (a : ℂ) ^ (-((1 / 2 : ℂ) + t * I)) =
      ((a ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * cexp (-(I * (t * Real.log a))) := by
    rw [Complex.cpow_def_of_ne_zero (ofReal_ne_zero.mpr ha.ne'), ← Complex.ofReal_log ha.le,
      Complex.ofReal_cpow ha.le, Complex.cpow_def_of_ne_zero (ofReal_ne_zero.mpr ha.ne'),
      ← Complex.ofReal_log ha.le, ← Complex.exp_add]
    congr 1; push_cast; ring
  rw [hcpow]
  have hphase : cexp (I * φ) * (cexp (↑π * I * a ^ 2) * cexp (-(I * (t * Real.log a)))) =
      cexp (I * (φ - rsThetaMain t - π / 8)) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    unfold rsThetaMain
    have hpa : (π : ℝ) * a ^ 2 = t / 2 := by rw [ha2]; field_simp
    have hta : t * Real.log a = t / 2 * Real.log t - t / 2 * Real.log (2 * π) := by rw [hlog]; ring
    have hc1 : (↑π * I * (a : ℂ) ^ 2 : ℂ) = I * ((π * a ^ 2 : ℝ) : ℂ) := by push_cast; ring
    rw [hc1, hpa]
    push_cast
    rw [show (t : ℂ) * (Real.log a : ℂ) = ((t * Real.log a : ℝ) : ℂ) by push_cast; ring, hta]
    push_cast; ring
  calc cexp (I * φ) * (cexp (↑π * I * a ^ 2) * (((a ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
        cexp (-(I * (t * Real.log a)))))
      = ((a ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
          (cexp (I * φ) * (cexp (↑π * I * a ^ 2) * cexp (-(I * (t * Real.log a))))) := by ring
    _ = _ := by rw [hphase]

/-! ## 4. The exact C0-corrected remainder -/



end RSInt

end

/-  RS_B3.lean -- lane RS, brick B3 (the explicit Riemann-Siegel remainder), part 2: the exact
    saddle-point reduction.  Mathlib-only (imports `RS_C0`).

    ## Vocabulary (height t > 0)

        a = rsAlpha t = sqrt(t / 2 pi),  N = rsNn t = floor a,  p = rsFrac t = a - N,
        rsThetaMain t = (t/2) log t - (t/2) log(2 pi) - t/2 - pi/8   (verbatim the corpus thetaMain),
        rsPsi p = cos(2 pi (p^2 - p - 1/16)) / cos(2 pi p)            (Gabcke's C0 = Riemann's Psi),
        rsRem t = -lineUp (N + 1/2) (x |-> rsG x x^(-(1/2 + i t)))    (the exact RS remainder, B2).

    By B2 (`completed_re_eq_rs_cos`), on the critical line
        Re completedRiemannZeta(1/2+it) = 2M ( sum_{n<=N} n^(-1/2) cos(phi - t log n) + Re(e^{i phi} rsRem t) ).

    ## What this file proves (no `sorry`, no `native_decide`, no new axioms)

      * `rsRem_factor` : moving the remainder line to the saddle point a and factoring out the
        stationary phase,
            rsRem t = (-1)^(N+1) e^{i pi a^2} a^(-s) (rsJ p + rsE1 a p),
        where rsJ is the tau = 2 Mordell integral (RS_C0) and rsE1 the error integral of the amplitude
        rsPhi a w - 1,  rsPhi a w = e^{2 pi i a w - pi i w^2} (1 + w/a)^(-s).
      * `rs_phase` : e^{i phi} e^{i pi a^2} a^(-s) = a^(-1/2) e^{i (phi - rsThetaMain t - pi/8)}.
      * `rs_remainder_exact` : the EXACT identity
            2 Re(e^{i phi} rsRem t) - (-1)^(N+1) a^(-1/2) Psi(p)
              = (-1)^(N+1) a^(-1/2) [ 2 Re(e^{-i pi/8}(e^{i delta} - 1) rsJ p)
                                      + 2 Re(e^{i (delta - pi/8)} rsE1 a p) ],   delta = phi - thetaMain t,
        so the C0-corrected remainder is controlled by |delta| |rsJ p| and |rsE1 a p| alone.

    conjecture1_proved = False.
-/


open Complex MeasureTheory Filter Topology Set
open scoped Real ComplexConjugate

noncomputable section

section
namespace RSInt
end RSInt
open RSInt

/-! ## 0. Vocabulary -/































/-! ## 1. Shifting the denominator by an integer -/



/-! ## 2. The factorization at the saddle point -/











/-! ## 3. The phase -/



/-! ## 4. The exact C0-corrected remainder -/


theorem solution {t : ℝ} (ht : 0 < t) (hp : 0 < rsFrac t)
    (hcos : Real.cos (2 * π * rsFrac t) ≠ 0) (φ : ℝ) :
    2 * (cexp (I * φ) * rsRem t).re -
        (-1 : ℝ) ^ (rsNn t + 1) * (rsAlpha t) ^ (-(1 / 2 : ℝ)) * rsPsi (rsFrac t) =
      (-1 : ℝ) ^ (rsNn t + 1) * (rsAlpha t) ^ (-(1 / 2 : ℝ)) *
        (2 * (cexp (-(↑π / 8 * I)) * (cexp (I * (φ - rsThetaMain t)) - 1) * rsJ (rsFrac t)).re +
          2 * (cexp (I * (φ - rsThetaMain t - π / 8)) * rsE1 (rsAlpha t) (rsFrac t)).re) := by
  have hC0 := rsJ_C0 hp rsFrac_lt_one hcos
  rw [rsRem_factor ht hp]
  set a := rsAlpha t
  set p := rsFrac t
  set J := rsJ p
  set E := rsE1 a p
  set q : ℝ := (-1 : ℝ) ^ (rsNn t + 1) * a ^ (-(1 / 2 : ℝ)) with hq
  have hmain : cexp (I * φ) * ((-1) ^ (rsNn t + 1) * cexp (↑π * I * a ^ 2) *
      ((a : ℂ) ^ (-((1 / 2 : ℂ) + t * I))) * (J + E)) =
      (q : ℂ) * (cexp (I * (φ - rsThetaMain t - π / 8)) * (J + E)) := by
    have hph := rs_phase ht φ
    rw [hq]
    push_cast
    calc cexp (I * φ) * ((-1) ^ (rsNn t + 1) * cexp (↑π * I * a ^ 2) *
          ((a : ℂ) ^ (-((1 / 2 : ℂ) + t * I))) * (J + E))
        = (-1) ^ (rsNn t + 1) * (cexp (I * φ) * (cexp (↑π * I * a ^ 2) *
            ((a : ℂ) ^ (-((1 / 2 : ℂ) + t * I))))) * (J + E) := by ring
      _ = (-1) ^ (rsNn t + 1) * ((((a ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) *
            cexp (I * (φ - rsThetaMain t - π / 8))) * (J + E) := by rw [hph]
      _ = _ := by ring
  rw [hmain, Complex.re_ofReal_mul]
  have hsplitexp : cexp (I * (φ - rsThetaMain t - π / 8)) =
      cexp (-(↑π / 8 * I)) * cexp (I * (φ - rsThetaMain t)) := by
    rw [← Complex.exp_add]; congr 1; ring
  have hXJ : cexp (I * (φ - rsThetaMain t - π / 8)) * J = cexp (-(↑π / 8 * I)) * J +
      cexp (-(↑π / 8 * I)) * (cexp (I * (φ - rsThetaMain t)) - 1) * J := by
    rw [hsplitexp]; ring
  have hre : (cexp (I * (φ - rsThetaMain t - π / 8)) * (J + E)).re =
      (cexp (-(↑π / 8 * I)) * J).re +
        (cexp (-(↑π / 8 * I)) * (cexp (I * (φ - rsThetaMain t)) - 1) * J).re +
        (cexp (I * (φ - rsThetaMain t - π / 8)) * E).re := by
    rw [mul_add, Complex.add_re, hXJ, Complex.add_re]
  rw [hre]
  unfold rsPsi
  rw [← hC0]
  ring
