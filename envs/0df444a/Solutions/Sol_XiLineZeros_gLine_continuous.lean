-- Prove2me | solution 1 for XiLineZeros.gLine_continuous
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T06:24:58.606758+00:00
-- url     : https://prove2.me/submissions/b8d86234-2d05-4ba0-903f-8a93bce02e3e

import Definitions.Def_ArdaRH65K_XiLineZeros
import Mathlib
/- telperion 0.1.6 | family XiLineZeros | input-hash 8bf933124b3cae44
   3 theorems, 11 generation-time self-checks passed.
   Regenerate & verify:  forge diff --family <module:attr> --manifest <manifest.json> --check
   DO NOT EDIT BY HAND — edits are flagged by the regeneration diff.  -/




open Complex

namespace XiLineZeros

/-!
# On-line zero localization of the completed Riemann zeta function (Stage 1 core)

Each theorem below states: given certified real enclosures of `Lambda(1/2 + i*t)`
(the documented Arb-certified NON-KERNEL input, as hypotheses) with alternating
signs, there exist strictly increasing reals in `[a, b]` at which
`completedRiemannZeta (1/2 + t*I) = 0`, i.e. `>= N` zeros of `Lambda` on the
critical line.  The proof lifts to the real part `gLine` (real on the line by the
Task-2 prelude `ZetaZeroLocalization.completedZeta_im_eq_zero`), uses its
continuity, and applies the intermediate value theorem on each sign-change
subinterval.

Note: `conjecture1_proved = False`.  This localizes individual nontrivial zeros ON
the critical line from certified enclosures; it does NOT prove RH.
-/

-- Real part of Lambda on the critical line.


-- The lifting point `1/2 + t*I` is never 0 nor 1 (its real part is 1/2).
theorem line_ne_zero (t : ℝ) : (1 / 2 + (t : ℂ) * Complex.I) ≠ 0 := by
  intro h
  have hre : ((1 / 2 + (t : ℂ) * Complex.I)).re = (0 : ℂ).re := by rw [h]
  simp at hre

theorem line_ne_one (t : ℝ) : (1 / 2 + (t : ℂ) * Complex.I) ≠ 1 := by
  intro h
  have hre : ((1 / 2 + (t : ℂ) * Complex.I)).re = (1 : ℂ).re := by rw [h]
  simp at hre

-- `gLine` is continuous on all of ℝ.  `completedRiemannZeta` is differentiable
-- (hence continuous) at each line point `1/2 + t*I`, which is never 0 nor 1.


-- On the line, Lambda equals its real part promoted to ℂ.











end XiLineZeros


/- telperion 0.1.6 | family XiLineZeros | input-hash 8bf933124b3cae44
   3 theorems, 11 generation-time self-checks passed.
   Regenerate & verify:  forge diff --family <module:attr> --manifest <manifest.json> --check
   DO NOT EDIT BY HAND — edits are flagged by the regeneration diff.  -/




open Complex

section
namespace XiLineZeros
end XiLineZeros
open XiLineZeros

/-!
# On-line zero localization of the completed Riemann zeta function (Stage 1 core)

Each theorem below states: given certified real enclosures of `Lambda(1/2 + i*t)`
(the documented Arb-certified NON-KERNEL input, as hypotheses) with alternating
signs, there exist strictly increasing reals in `[a, b]` at which
`completedRiemannZeta (1/2 + t*I) = 0`, i.e. `>= N` zeros of `Lambda` on the
critical line.  The proof lifts to the real part `gLine` (real on the line by the
Task-2 prelude `ZetaZeroLocalization.completedZeta_im_eq_zero`), uses its
continuity, and applies the intermediate value theorem on each sign-change
subinterval.

Note: `conjecture1_proved = False`.  This localizes individual nontrivial zeros ON
the critical line from certified enclosures; it does NOT prove RH.
-/

-- Real part of Lambda on the critical line.


-- The lifting point `1/2 + t*I` is never 0 nor 1 (its real part is 1/2).




-- `gLine` is continuous on all of ℝ.  `completedRiemannZeta` is differentiable
-- (hence continuous) at each line point `1/2 + t*I`, which is never 0 nor 1.
theorem solution : Continuous gLine := by
  have hline : Continuous (fun t : ℝ => (1 / 2 + (t : ℂ) * Complex.I)) := by
    fun_prop
  have hZeta : Continuous (fun t : ℝ => completedRiemannZeta (1 / 2 + (t : ℂ) * Complex.I)) := by
    rw [continuous_iff_continuousAt]
    intro t
    have hd : DifferentiableAt ℂ completedRiemannZeta (1 / 2 + (t : ℂ) * Complex.I) :=
      differentiableAt_completedZeta (line_ne_zero t) (line_ne_one t)
    exact ContinuousAt.comp (g := completedRiemannZeta)
      (f := fun t : ℝ => (1 / 2 + (t : ℂ) * Complex.I)) hd.continuousAt
      (hline.continuousAt (x := t))
  exact Complex.continuous_re.comp hZeta
