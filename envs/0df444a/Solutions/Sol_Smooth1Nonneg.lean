-- Prove2me | solution 1 for Smooth1Nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-07-29T18:15:33.130481+00:00
-- url     : https://prove2.me/submissions/fbf451eb-4fdd-4321-843c-776c34999afb

import Batteries.Tactic.Lemma
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Analysis.MellinTransform
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Tactic.Bound
import Mathlib.Tactic.GCongr
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.InnerProductSpace.Basic
import Definitions.Def_MellinCalculus_defs
import Theorems.Thm_DeltaSpikeNonNeg_of_NonNeg

open scoped ContDiff

set_option lang.lemmaCmd true

-- TODO: move near `MeasureTheory.setIntegral_prod`

-- How to deal with this coercion?... Ans: (f ·)
--- noncomputable def funCoe (f : ℝ → ℝ) : ℝ → ℂ := fun x ↦ f x

open Complex Topology Filter Real MeasureTheory Set

variable {𝕂 : Type*} [RCLike 𝕂]

-- TODO: generalize to `RCLike`

local notation (name := mellintransform) "𝓜" => mellin

-- filter-free version:

-- This lemma might not be necessary, but the RHS is supported on [0, infinity), which makes
-- results like `support_MellinConvolution_subsets` easier to apply.

/-% ** Wrong delimiters on purpose, no need to include this in the LaTeX outline
\begin{lemma}[Smooth1Properties_estimate]\label{Smooth1Properties_estimate}
\lean{Smooth1Properties_estimate}\leanok
For $\epsilon>0$,
$$
  \log2>\frac{1-2^{-\epsilon}}\epsilon
$$
\end{lemma}
%-/

theorem MellinConvNonNeg_of_NonNeg {f g : ℝ → ℝ} (f_nonneg : ∀ x > 0, 0 ≤ f x)
    (g_nonneg : ∀ x > 0, 0 ≤ g x) {x : ℝ} (xpos : 0 < x) :
    0 ≤ MellinConvolution f g x := by
  dsimp [MellinConvolution]
  apply MeasureTheory.setIntegral_nonneg
  · exact measurableSet_Ioi
  · intro y ypos; simp only [mem_Ioi] at ypos
    have : 0 ≤ f y := f_nonneg _ ypos
    have : 0 < x / y := by positivity
    have : 0 ≤ g (x / y) := g_nonneg _ this
    positivity

theorem solution {ν : ℝ → ℝ} (νnonneg : ∀ x > 0, 0 ≤ ν x) {ε x : ℝ}
    (xpos : 0 < x) (εpos : 0 < ε) : 0 ≤ Smooth1 ν ε x := by
  dsimp [Smooth1]
  apply MellinConvNonNeg_of_NonNeg ?_ ?_ xpos
  · intro y hy; by_cases h : y ≤ 1 <;> simp [h, hy]
  · intro y ypos; exact DeltaSpikeNonNeg_of_NonNeg νnonneg ypos εpos
