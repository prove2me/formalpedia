-- Prove2me | solution 1 for ParameterizedCalculus.family_comp_hasDerivAt
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-06T14:52:46.563975+00:00
-- url     : https://prove2.me/submissions/7d468ca9-9411-4291-b7a5-35b4e7145ae5

import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Prod

open scoped ContDiff

theorem solution {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : ℝ → E → F)
    (hf : ContDiff ℝ ∞ (fun p : ℝ × E => f p.1 p.2))
    (γ : ℝ → E) (t : ℝ) (γ' : E) (hγ : HasDerivAt γ γ' t) :
    HasDerivAt (fun s => f s (γ s))
      (deriv (fun s => f s (γ t)) t + fderiv ℝ (f t) (γ t) γ') t := by
  let A := fderiv ℝ (fun p : ℝ × E => f p.1 p.2) (t, γ t)
  have hA : HasFDerivAt (fun p : ℝ × E => f p.1 p.2) A (t, γ t) :=
    (hf.differentiable (by simp)).differentiableAt.hasFDerivAt
  have htime : HasDerivAt (fun s => f s (γ t)) (A (1, 0)) t := by
    simpa [Function.comp_def] using
      hA.comp_hasDerivAt t ((hasDerivAt_id t).prodMk (hasDerivAt_const t (γ t)))
  have hspace : HasFDerivAt (f t)
      (A.comp (ContinuousLinearMap.inr ℝ ℝ E)) (γ t) := by
    simpa [Function.comp_def] using hA.comp (γ t) (hasFDerivAt_prodMk_right t (γ t))
  have htotal := hA.comp_hasDerivAt t ((hasDerivAt_id t).prodMk hγ)
  have hsplit : A (1, γ') = A (1, 0) + A (0, γ') := by
    rw [← map_add]
    simp
  simpa [Function.comp_def, htime.deriv, hspace.fderiv, hsplit,
    ContinuousLinearMap.comp_apply] using htotal
