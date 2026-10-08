-- Prove2me | solution 1 for RetailVariety.Fashion.g_convex
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T22:30:40.711062+00:00
-- url     : https://prove2.me/submissions/ebe0009f-6562-44f3-acde-e22994105fa8

import Mathlib
import Definitions.Def_RetailVariety_Fashion_ProofObjects
open RetailVariety.Fashion

/-- p. 1506: for `L > 0`, `g` and `g^T` are convex on `[0, ∞)`, `g^T(0) = 0`, and `g(0) = 0` when
`0 < β`. -/
theorem solution (p c lam σ β L : ℝ) (hc : 0 < c) (hcp : c < p) (hlam : 0 < lam)
    (hσ : 0 < σ) (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hL : 0 < L) :
    ConvexOn ℝ (Set.Ici 0) (gFun p c lam σ β L) ∧
      ConvexOn ℝ (Set.Ici 0) (gFunT p c lam L) ∧
      gFunT p c lam L 0 = 0 ∧
      (0 < β → gFun p c lam σ β L 0 = 0) := by


  have hpp : 0 < p := hc.trans hcp
  have hcoef : 0 ≤ safetyCoeff p c lam σ β / L ^ β := by
    unfold safetyCoeff
    positivity
  have hlin : ConvexOn ℝ (Set.Ici 0) (fun x : ℝ => (p-c)*lam/L*x) := by
    refine ⟨convex_Ici 0, ?_⟩
    intro x hx y hy a b ha hb hab
    simp only [smul_eq_mul]
    ring_nf
    rfl
  have hg := hlin.sub ((Real.concaveOn_rpow hβ0 hβ1.le).smul hcoef)
  have ha : ConvexOn ℝ (Set.Ici 0) (fun x : ℝ => p*x-c*L) := by
    refine ⟨convex_Ici 0, ?_⟩
    intro x hx y hy a b ha hb hab
    simp only [smul_eq_mul]
    nlinarith [congrArg (fun t : ℝ => t*(c*L)) hab]
  have hm := ha.sup (convexOn_const (0 : ℝ) (convex_Ici 0))
  refine ⟨hg, hm.smul (div_nonneg hlam.le hL.le), ?_, ?_⟩
  · simp [gFunT, max_eq_right (by nlinarith : -(c*L) ≤ 0)]
  · intro hb
    simp [gFun, Real.zero_rpow hb.ne']
#print axioms solution

