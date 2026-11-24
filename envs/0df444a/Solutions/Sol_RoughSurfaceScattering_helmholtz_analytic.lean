-- Prove2me | solution 1 for RoughSurfaceScattering.helmholtz_analytic
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-24T05:48:56.715101+00:00
-- url     : https://prove2.me/submissions/6986cf26-ada0-4e35-9fa9-874577b3eeaa
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_RoughSurfaceScattering_Basic
import Theorems.Thm_RoughSurfaceScattering_harmonic_analytic_R3
import Theorems.Thm_RoughSurfaceScattering_helmholtz_descent_harmonic

open MeasureTheory
open RoughSurfaceScattering

/-- The embedding `ι(x₁, x₂) = (x₁, x₂, 0)` of the plane into `ℝ³`. -/
noncomputable def embR3 : R2 →L[ℝ] EuclideanSpace ℝ (Fin 3) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => !₂[x 0, x 1, 0]
      map_add' := fun x y => by ext i; fin_cases i <;> simp
      map_smul' := fun c x => by ext i; fin_cases i <;> simp }

lemma embR3_apply (x : R2) : embR3 x = !₂[x 0, x 1, 0] := rfl

theorem solution (k : ℝ) (G : Set R2) (hG : IsOpen G) (u : R2 → ℂ)
    (hu : ContDiffOn ℝ 2 u G) (hH : IsHelmholtzOn G k u) :
    AnalyticOnNhd ℝ u G := by
  have hv := helmholtz_descent_harmonic k G hG u hu hH
  set v : EuclideanSpace ℝ (Fin 3) → ℂ :=
    fun y => u (pt (y 0) (y 1)) * (Real.exp (k * y 2) : ℂ)
  -- `u = v ∘ ι`
  have hpt : ∀ x : R2, pt ((embR3 x) 0) ((embR3 x) 1) = x := by
    intro x; ext i; fin_cases i <;> simp [embR3_apply, pt]
  have hcomp : u = v ∘ embR3 := by
    funext x
    simp only [Function.comp_apply, v, hpt x]
    simp [embR3_apply]
  intro x hx
  have hvx : AnalyticAt ℝ v (embR3 x) :=
    harmonic_analytic_R3 v (embR3 x) (hv (embR3 x) (by simpa [hpt x] using hx))
  rw [hcomp]
  exact hvx.comp (embR3.analyticAt x)
