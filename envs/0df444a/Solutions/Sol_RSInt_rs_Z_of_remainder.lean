-- Prove2me | solution 1 for RSInt.rs_Z_of_remainder
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T06:41:34.487664+00:00
-- url     : https://prove2.me/submissions/dc97539a-006c-42fb-93ce-203ff14a17f6

import Definitions.Def_ArdaRH65K_DlvpTheta
import Definitions.Def_ArdaRH65K_RSTheta
import Definitions.Def_ArdaRH65K_RS_B2
import Definitions.Def_ArdaRH65K_RS_B3
import Definitions.Def_ArdaRH65K_RS_B3Sharp
import Definitions.Def_ArdaRH65K_RS_C0
import Definitions.Def_ArdaRH65K_RS_Entire
import Definitions.Def_ArdaRH65K_RS_Fold
import Definitions.Def_ArdaRH65K_RS_Kernel
import Definitions.Def_ArdaRH65K_RS_Mellin
import Definitions.Def_ArdaRH65K_RS_Strip
import Definitions.Def_ArdaRH65K_ThetaConverge
import Definitions.Def_ArdaRH65K_ThetaValue
import Definitions.Def_ArdaRH65K_XiLineZeros
import Mathlib
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Theorems.Thm_RSDesignTheta_theta_sub_thetaMain
import Theorems.Thm_RSInt_completed_re_eq_rs_cos
import Theorems.Thm_ThetaConverge_convergence_obligation
import Theorems.Thm_ZeroSignDecomp_gamma_r_polar_t
/-  RS_Bridge.lean -- lane RS, brick B3 part 4: the Riemann-Siegel formula for Hardy's Z with the
    C0 term and an explicit remainder, HYPOTHESIS-FREE on the phase (imports `RS_B3Bound`, the
    island's `RSTheta` Stirling bracket and `ZeroSignDecomp_t14` polar form; all read-only).

    ## The headline (no `sorry`, no `native_decide`, no new axioms)

      `rs_Z_C0` : for t >= 10000, 0 < p = rsFrac t, cos(2 pi p) ≠ 0, there are M > 0 and phi with
          Gammaℝ(1/2+it) = M e^{i phi},   |phi - thetaMain t| <= 1/t,   and
          | Re completedRiemannZeta(1/2+it) / M
              - ( 2 sum_{n<=N} n^(-1/2) cos(phi - t log n) + (-1)^(N+1) (t/2pi)^(-1/4) Psi(p) ) |
            <= 2 t^(-3/4),
      N = floor(sqrt(t/2pi)), p = sqrt(t/2pi) - N, Psi(p) = cos(2 pi (p^2 - p - 1/16)) / cos(2 pi p).

    The phase phi = Lam - (t/2) log pi is the island's branch-correct Riemann-Siegel theta
    (`ThetaConverge.convergence_obligation` + `ZeroSignDecomp.gamma_r_polar_t`), and the bound
    |phi - thetaMain t| <= 1/t is `RSDesignTheta.theta_sub_thetaMain`.  The quotient on the left is
    Hardy's Z(t) (Re Lambda(1/2+it) = M Z(t), M = |Gammaℝ(1/2+it)| > 0): its sign is the sign of the
    island's `gLine t`, so a sign certificate for gLine at height t >= 10000 now needs only the
    finite main sum, one Psi value and the margin 2 t^(-3/4).

    conjecture1_proved = False.  An explicit finite-height formula; nothing here bears on the
    Riemann Hypothesis.
-/




open Complex MeasureTheory Filter Topology Set
open scoped Real ComplexConjugate

noncomputable section

namespace RSInt

theorem rsThetaMain_eq_thetaMain (t : ℝ) : rsThetaMain t = ZeroFreeBridge.thetaMain t := rfl



end RSInt

end

/-  RS_BridgeSharp.lean -- lane RS, brick B3 part 4 SHARPENED (RSC0 Phase 2): the Riemann-Siegel
    formula for Hardy's Z with the C0 term and the SHARPENED explicit remainders of `RS_B3Sharp`,
    phase discharged hypothesis-free exactly as in `RS_Bridge` / `RSSeam_Bridge` (imports
    `RS_B3Sharp`, `RS_Bridge`; all read-only, nothing existing is edited).

    ## The headlines (no `sorry`, no `native_decide`, no new axioms)

      `RSInt.rs_Z_C0'` : for t >= 4250, 0 < p = rsFrac t, cos(2 pi p) ≠ 0, there are M > 0 and phi with
          Gammaℝ(1/2+it) = M e^{i phi},   |phi - thetaMain t| <= 1/t,   and
          | Re completedRiemannZeta(1/2+it) / M
              - ( 2 sum_{n<=N} n^(-1/2) cos(phi - t log n) + (-1)^(N+1) (t/2pi)^(-1/4) Psi(p) ) |
            <= (3/5) t^(-3/4).
      `RSSeam.rs_Z_C0_seam'` : the same for t >= 509 with (21/25) t^(-3/4).
      Same statement shape as `RSInt.rs_Z_C0` (2 t^(-3/4), t >= 10000) and `RSSeam.rs_Z_C0_seam`
      ((13/5) t^(-3/4), t >= 509); those two statements are re-derived here from the sharpened
      remainders as `RSInt.rs_Z_C0_of_sharp` and `RSSeam.rs_Z_C0_seam_of_sharp`.

    `rs_Z_of_remainder` is the proof of `RSInt.rs_Z_C0` with the remainder constant abstracted:
    any bound C on the C0-corrected remainder, valid for every phase within 1/t of thetaMain, is a
    bound on the Z formula with the island's branch-correct theta.

    conjecture1_proved = False.  An explicit finite-height formula; nothing here bears on the
    Riemann Hypothesis.
-/



open Complex MeasureTheory Filter Topology Set
open scoped Real ComplexConjugate

noncomputable section

section
namespace RSInt
end RSInt
open RSInt


theorem solution {t C : ℝ} (ht0 : 0 < t)
    (hrem : ∀ φ : ℝ, |φ - rsThetaMain t| ≤ 1 / t →
      |2 * (cexp (I * φ) * rsRem t).re -
        (-1 : ℝ) ^ (rsNn t + 1) * (t / (2 * π)) ^ (-(1 / 4 : ℝ)) * rsPsi (rsFrac t)| ≤ C) :
    ∃ M φ : ℝ, 0 < M ∧ Gammaℝ ((1 / 2 : ℂ) + t * I) = (M : ℂ) * cexp (I * φ) ∧
      |φ - rsThetaMain t| ≤ 1 / t ∧
      |(completedRiemannZeta ((1 / 2 : ℂ) + t * I)).re / M -
          (2 * ∑ n ∈ Finset.Icc 1 (rsNn t), (n : ℝ) ^ (-(1 / 2 : ℝ)) * Real.cos (φ - t * Real.log n) +
            (-1 : ℝ) ^ (rsNn t + 1) * (t / (2 * π)) ^ (-(1 / 4 : ℝ)) * rsPsi (rsFrac t))| ≤ C := by
  have hGne : Complex.Gamma (((1 / 4 : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * I) ≠ 0 := by
    apply Complex.Gamma_ne_zero
    intro m hcontra
    have him := congrArg Complex.im hcontra
    simp at him
    linarith
  obtain ⟨Λ, hΛtend, hbranch⟩ :=
    ThetaConverge.convergence_obligation (1 / 4) (t / 2) (by norm_num) hGne
  obtain ⟨M, hM, hpolar⟩ := ZeroSignDecomp.gamma_r_polar_t t ht0.ne' Λ hbranch
  have hθ := RSDesignTheta.theta_sub_thetaMain t ht0 Λ hΛtend
  set φ : ℝ := Λ - t / 2 * Real.log Real.pi with hφ
  have hφb : |φ - rsThetaMain t| ≤ 1 / t := by
    rw [rsThetaMain_eq_thetaMain]; exact hθ
  refine ⟨M, φ, hM, hpolar, hφb, ?_⟩
  have hN : ((rsNn t : ℕ) : ℝ) < (rsNn t : ℝ) + 1 / 2 := by linarith
  have hN' : (rsNn t : ℝ) + 1 / 2 < (rsNn t : ℝ) + 1 := by linarith
  have hre := completed_re_eq_rs_cos t (rsNn t) hN hN' hpolar
  have hrem' : -lineUp ((rsNn t : ℝ) + 1 / 2) (fun x => rsG x * x ^ (-((1 / 2 : ℂ) + t * I))) =
      rsRem t := rfl
  rw [hrem'] at hre
  rw [hre]
  have hC0 := hrem φ hφb
  have e : 2 * M * ((∑ n ∈ Finset.Icc 1 (rsNn t), (n : ℝ) ^ (-(1 / 2 : ℝ)) *
        Real.cos (φ - t * Real.log n)) + (cexp (I * φ) * rsRem t).re) / M -
      (2 * ∑ n ∈ Finset.Icc 1 (rsNn t), (n : ℝ) ^ (-(1 / 2 : ℝ)) * Real.cos (φ - t * Real.log n) +
        (-1 : ℝ) ^ (rsNn t + 1) * (t / (2 * π)) ^ (-(1 / 4 : ℝ)) * rsPsi (rsFrac t)) =
      2 * (cexp (I * φ) * rsRem t).re -
        (-1 : ℝ) ^ (rsNn t + 1) * (t / (2 * π)) ^ (-(1 / 4 : ℝ)) * rsPsi (rsFrac t) := by
    field_simp
    ring
  rw [e]
  exact hC0
