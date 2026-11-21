-- Prove2me | solution 1 for RiemannMasullo.directSumDifference_apply
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-20T22:40:55.423345+00:00
-- url     : https://prove2.me/submissions/60ce5e2c-499b-4b72-b8e5-c3d59aac7b45

-- Adapted from mccorvie/riemann-masullo, Apache-2.0.
-- https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppC_LCTVS/Sec1.lean#L437-L460
import Definitions.Def_RiemannMasullo_AppC_InductiveLimits

open RiemannMasullo
open Set Filter Topology TopologicalSpace Bornology
open scoped Pointwise DirectSum
variable {E : Type*} [AddCommGroup E] [Module ℂ E] [tE : TopologicalSpace E]
variable {X : ℕ → Type*} [∀ k, AddCommGroup (X k)] [∀ k, Module ℂ (X k)]
  [∀ k, TopologicalSpace (X k)]

theorem solution (j : ∀ k, X k →L[ℂ] X (k+1)) (x : ⨁ k, X k) :
    directSumDifference j x 0 = x 0 ∧
      ∀ k, directSumDifference j x (k+1) = x (k+1) - j k (x k) := by
  let shift := DirectSum.toModule ℂ ℕ (⨁ k, X k) (fun k ↦
    (DirectSum.lof ℂ ℕ X (k+1)).comp (j k).toLinearMap)
  have hzero : shift x 0 = 0 := by
    suffices (DirectSum.component ℂ ℕ X 0).comp shift = 0 from LinearMap.congr_fun this x
    apply DirectSum.linearMap_ext
    intro i
    ext y : 1
    simp [shift, DirectSum.component.of]
  have hsucc (k : ℕ) : shift x (k+1) = j k (x k) := by
    suffices (DirectSum.component ℂ ℕ X (k+1)).comp shift =
        (j k).toLinearMap.comp (DirectSum.component ℂ ℕ X k) from LinearMap.congr_fun this x
    apply DirectSum.linearMap_ext
    intro i
    ext y : 1
    by_cases h : i = k
    · subst i
      simp [shift]
    · simp [shift, DirectSum.component.of, h]
  change (x - shift x) 0 = x 0 ∧
    ∀ k, (x - shift x) (k+1) = x (k+1) - j k (x k)
  simp [DirectSum.sub_apply, hzero, hsucc]
