-- Prove2me | solution 1 for ZetaDerivUpperBnd_prime
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-07-29T18:47:14.945129+00:00
-- url     : https://prove2.me/submissions/6f9e26da-2bb4-4407-a250-9851215cc28b

import Batteries.Tactic.Lemma
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.NumberTheory.AbelSummation
import Mathlib.Order.Filter.ZeroAndBoundedAtFilter
import Mathlib.Order.Interval.Set.Monotone
import Mathlib.Tactic.Abel
import Mathlib.Tactic.LinearCombinationPrime
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Definitions.Def_EulerMaclaurin_defs
import Definitions.Def_Fourier_defs
import Definitions.Def_Rectangle_defs
import Definitions.Def_ResidueCalcOnRectangles_defs
import Definitions.Def_ZetaBounds_defs
import Theorems.Thm_DerivUpperBnd_aux1
import Theorems.Thm_DerivUpperBnd_aux2
import Theorems.Thm_DerivUpperBnd_aux3
import Theorems.Thm_DerivUpperBnd_aux4
import Theorems.Thm_DerivUpperBnd_aux5
import Theorems.Thm_DerivUpperBnd_aux6
import Theorems.Thm_DerivUpperBnd_aux7
import Theorems.Thm_UpperBnd_aux

set_option lang.lemmaCmd true

open Complex Topology Filter Interval Set Asymptotics

local notation (name := riemannzeta) "ζ" => riemannZeta
local notation (name := derivriemannzeta) "ζ'" => deriv riemannZeta

-- Main theorem: if functions agree on a punctured set, their derivatives agree there too

/- New two theorems to be proven -/

-- Alternative cleaner proof using more direct approach

/- The set should be open so that f'(p) = O(1) for all p ∈ U -/

/-- We use `ζ` to denote the Rieman zeta function and `ζ₀` to denote the alternative Rieman zeta
function. -/
local notation (name := riemannzeta0) "ζ₀" => riemannZeta0

-- move near `Real.differentiableAt_rpow_const_of_ne`

-- MOVE TO MATHLIB near `differentiableAt_riemannZeta`

theorem solution {A σ t : ℝ} (hA : A ∈ Ioc 0 (1 / 2)) (t_gt : 3 < |t|)
    (hσ : σ ∈ Icc (1 - A / Real.log |t|) 2) :
    let C := Real.exp A * 59;
    let N := ⌊|t|⌋₊;
    let s := σ + t * I;
    ‖∑ n ∈ Finset.range (N + 1), -1 / (n : ℂ) ^ s * (Real.log n)‖ +
      ‖-(N : ℂ) ^ (1 - s) / (1 - s) ^ 2‖ +
      ‖(Real.log N) * (N : ℂ) ^ (1 - s) / (1 - s)‖ +
      ‖(Real.log N) * (N : ℂ) ^ (-s) / 2‖ +
      ‖(1 * ∫ (x : ℝ) in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-s - 1))‖ +
      ‖s * ∫ (x : ℝ) in Ioi (N : ℝ),
        (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-s - 1) * -(Real.log x)‖
        ≤ C * Real.log |t| ^ 2 := by
  intros C N s
  obtain ⟨Npos, N_le_t, logt_gt, σ_gt, _, neOne⟩ := UpperBnd_aux hA t_gt hσ.1
  replace σ_gt : 1 / 2 < σ := by linarith [hA.2]
  calc _ ≤ Real.exp A * 2 * (Real.log |t|) ^ 2 +
      ‖-(N : ℂ) ^ (1 - s) / (1 - s) ^ 2‖ +
      ‖(Real.log N) * (N : ℂ) ^ (1 - s) / (1 - s)‖ +
      ‖(Real.log N) * (N : ℂ) ^ (-s) / 2‖ +
      ‖(1 * ∫ (x : ℝ) in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-s - 1))‖ +
      ‖s * ∫ (x : ℝ) in Ioi (N : ℝ),
        (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-s - 1) * -(Real.log x)‖ := by
        gcongr; exact DerivUpperBnd_aux1 hA hσ.1 t_gt (by simp : (2 : ℝ) ≤ 2)
    _ ≤ Real.exp A * 2 * (Real.log |t|) ^ 2 +
      Real.exp A * 2 * (1 / 3) +
      ‖(Real.log N) * (N : ℂ) ^ (1 - s) / (1 - s)‖ +
      ‖(Real.log N) * (N : ℂ) ^ (-s) / 2‖ +
      ‖(1 * ∫ (x : ℝ) in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-s - 1))‖ +
      ‖s * ∫ (x : ℝ) in Ioi (N : ℝ),
        (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-s - 1) * -(Real.log x)‖ := by
        gcongr; exact DerivUpperBnd_aux2 t_gt hσ Npos N_le_t neOne σ_gt
    _ ≤ Real.exp A * 2 * (Real.log |t|) ^ 2 +
      Real.exp A * 2 * (1 / 3) +
      Real.exp A * 2 * (Real.log |t|) +
      ‖(Real.log N) * (N : ℂ) ^ (-s) / 2‖ +
      ‖(1 * ∫ (x : ℝ) in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-s - 1))‖ +
      ‖s * ∫ (x : ℝ) in Ioi (N : ℝ),
        (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-s - 1) * -(Real.log x)‖ := by
        gcongr; exact DerivUpperBnd_aux3 t_gt hσ Npos N_le_t neOne σ_gt
    _ ≤ Real.exp A * 2 * (Real.log |t|) ^ 2 +
      Real.exp A * 2 * (1 / 3) +
      Real.exp A * 2 * (Real.log |t|) +
      Real.exp A * (Real.log |t|) +
      ‖(1 * ∫ (x : ℝ) in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-s - 1))‖ +
      ‖s * ∫ (x : ℝ) in Ioi (N : ℝ),
        (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-s - 1) * -(Real.log x)‖ := by
        gcongr; exact DerivUpperBnd_aux4 t_gt hσ Npos N_le_t neOne σ_gt
    _ ≤ Real.exp A * 2 * (Real.log |t|) ^ 2 +
      Real.exp A * 2 * (1 / 3) +
      Real.exp A * 2 * (Real.log |t|) +
      Real.exp A * (Real.log |t|) +
      1 / 3 * (2 * |t| * N ^ (-σ) / σ) +
      ‖s * ∫ (x : ℝ) in Ioi (N : ℝ),
        (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-s - 1) * -(Real.log x)‖ := by
        gcongr; exact DerivUpperBnd_aux5 t_gt hσ Npos σ_gt
    _ ≤ Real.exp A * 2 * (Real.log |t|) ^ 2 +
      Real.exp A * 2 * (1 / 3) +
      Real.exp A * 2 * (Real.log |t|) +
      Real.exp A * (Real.log |t|) +
      1 / 3 * (2 * (8 * Real.exp A)) +
      ‖s * ∫ (x : ℝ) in Ioi (N : ℝ),
        (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-s - 1) * -(Real.log x)‖ := by
        gcongr; exact DerivUpperBnd_aux6 t_gt hσ Npos N_le_t neOne σ_gt
    _ ≤ Real.exp A * 2 * (Real.log |t|) ^ 2 +
      Real.exp A * 2 * (1 / 3) +
      Real.exp A * 2 * (Real.log |t|) +
      Real.exp A * (Real.log |t|) +
      1 / 3 * (2 * (8 * Real.exp A)) +
      (6 * |t| * N ^ (-σ) / σ) * (Real.log |t|) := by
        gcongr; exact DerivUpperBnd_aux7 t_gt hσ Npos N_le_t neOne σ_gt
    _ ≤ Real.exp A * 2 * (Real.log |t|) ^ 2 +
      Real.exp A * 2 * (1 / 3) +
      Real.exp A * 2 * (Real.log |t|) +
      Real.exp A * (Real.log |t|) +
      1 / 3 * (2 * (8 * Real.exp A)) +
      (6 * (8 * Real.exp A)) * (Real.log |t|) := by
        gcongr; convert mul_le_mul_of_nonneg_left (DerivUpperBnd_aux6 t_gt hσ Npos N_le_t neOne σ_gt) (by norm_num : (0 : ℝ) ≤ 3) using 1 <;> ring
    _ ≤ _ := by
      simp only [C]
      ring_nf
      rw [(by ring : A.exp * |t|.log ^ 2 * 59 = A.exp * |t|.log ^ 2 * 6 + A.exp * |t|.log ^ 2 * 51 +
        A.exp * |t|.log ^ 2 * 2)]
      nth_rewrite 1 [← mul_one A.exp]
      gcongr
      swap
      · nth_rewrite 1 [← mul_one |t|.log, (by ring : |t|.log ^ 2 = |t|.log * |t|.log)]
        gcongr
      nlinarith

-- **Another AlphaProof collaboration (thanks to Thomas Hubert!)**

-- **End collaboration 6/20/25**

/-% ** Bad delimiters on purpose **
Annoying: we have reciprocals of $log |t|$ in the bounds, and we've assumed that $|t|>3$; but we
want to make things uniform in $t$. Let's change to things like $log (|t|+3)$ instead of $log |t|$.
\begin{lemma}[LogLeLog]\label{LogLeLog}\lean{LogLeLog}\leanok
There is a constant $C>0$ so that for all $t>3$,
$$
1/\log t \le C / \log (t + 3).
$$
\end{lemma}
%-/
/-%
\begin{proof}
Write
$$
\log (t + 3) = \log t + \log (1 + 3/t) = \log t + O(1/t).
$$
Then we can bound $1/\log t$ by $C / \log (t + 3)$ for some constant $C>0$.
\end{proof}
%-/

-- **Begin collaboration with the Alpha Proof team! 5/29/25**

-- **End collaboration**

open ArithmeticFunction (vonMangoldt)
local notation "Λ" => vonMangoldt
--TODO generalize to any LSeries with nonnegative coefficients
