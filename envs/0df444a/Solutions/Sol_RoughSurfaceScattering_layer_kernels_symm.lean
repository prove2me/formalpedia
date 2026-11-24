-- Prove2me | solution 1 for RoughSurfaceScattering.layer_kernels_symm
-- status  : ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-24T12:17:01.061032+00:00
-- url     : https://prove2.me/submissions/8f3235b6-752a-4861-adb1-507aabd7f2f0

import Mathlib
import Definitions.Def_RoughSurfaceScattering_Basic
import Theorems.Thm_RoughSurfaceScattering_Gimp_symm

open MeasureTheory
open RoughSurfaceScattering

/-- Kernel transposition for any symmetric kernel. -/
lemma kernels_symm_of_symm (f : ℝ → ℝ) (K : R2 → R2 → ℂ) (hK : ∀ x y, K x y = K y x)
    (s t : ℝ) :
    kerGam f K s t = kerGam f K t s ∧ dnyGam f K s t = dnxGam f K t s := by
  refine ⟨hK _ _, ?_⟩
  have hfun : (fun y => K (gpt f s) y) = fun x => K x (gpt f s) := funext fun y => hK _ _
  simp only [dnyGam, dnxGam, hfun]

theorem solution (f : ℝ → ℝ) (k a σ : ℝ) (s t : ℝ) :
    kerGam f (Gimp k a σ) s t = kerGam f (Gimp k a σ) t s ∧
      dnyGam f (Gimp k a σ) s t = dnxGam f (Gimp k a σ) t s :=
  kernels_symm_of_symm f (Gimp k a σ) (fun x y => Gimp_symm k a σ x y) s t
