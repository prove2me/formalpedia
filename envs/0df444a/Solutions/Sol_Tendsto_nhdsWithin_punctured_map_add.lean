-- Prove2me | solution 1 for Tendsto_nhdsWithin_punctured_map_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-07-29T18:58:42.546457+00:00
-- url     : https://prove2.me/submissions/b901e028-5f7e-449a-938f-e4549c9fd2d4

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

theorem solution {f : ℝ → ℝ} (a x : ℝ)
    (f_mono : StrictMono f) (f_iso : Isometry f) :
    Tendsto (fun y ↦ f y + a) (𝓝[>] x) (𝓝[>] (f x + a)) := by
  refine tendsto_iff_forall_eventually_mem.mpr ?_
  intro v hv
  simp only [mem_nhdsWithin] at hv
  obtain ⟨u, hu, hu2, hu3⟩ := hv
  let t := {x | f x + a ∈ u}
  have : t ∩ Ioi x ∈ 𝓝[>] x := by
    simp only [mem_nhdsWithin]
    use t
    simp only [subset_inter_iff, inter_subset_left, inter_subset_right, and_self,
      and_true, t, mem_setOf_eq]
    refine ⟨?_, by simp [hu2]⟩
    simp only [Metric.isOpen_iff, gt_iff_lt, mem_setOf_eq] at hu ⊢
    intro x hx
    obtain ⟨ε, εpos, hε⟩ := hu (f x + a) hx
    simp only [Metric.ball, setOf_subset_setOf] at hε ⊢
    exact ⟨ε, εpos, fun _ hy ↦ hε (by simp [isometry_iff_dist_eq.mp f_iso, hy])⟩
  filter_upwards [this]
  intro b hb
  simp only [mem_inter_iff, mem_setOf_eq, mem_Ioi, t] at hb
  refine hu3 ?_
  simp only [mem_inter_iff, mem_Ioi, add_lt_add_iff_right]
  exact ⟨hb.1, f_mono hb.2⟩

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
