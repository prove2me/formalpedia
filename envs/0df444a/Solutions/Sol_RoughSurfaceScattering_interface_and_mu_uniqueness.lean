-- Prove2me | solution 1 for RoughSurfaceScattering.interface_and_mu_uniqueness
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-24T03:53:37.45814+00:00
-- url     : https://prove2.me/submissions/c57c7d73-32ec-42a6-98ba-7e4ca119d0be
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_RoughSurfaceScattering_Basic
import Theorems.Thm_RoughSurfaceScattering_interface_uniqueness
import Theorems.Thm_RoughSurfaceScattering_mu_uniqueness

open MeasureTheory
open RoughSurfaceScattering

theorem solution (f1 f2 : ℝ → ℝ) (hf1 : IsBC1Alpha 1 f1) (hf2 : IsBC1Alpha 1 f2)
    (lam1 lam2 : ℝ) (hlam1 : 0 < lam1 ∧ lam1 ≤ 1) (hlam2 : 0 < lam2 ∧ lam2 ≤ 1)
    (hf1' : IsC2Lambda lam1 f1) (hf2' : IsC2Lambda lam2 f2)
    (kp k1 k2 μ1 μ2 : ℝ) (hpar1 : ParamCond kp k1 μ1) (hpar2 : ParamCond kp k2 μ2)
    (U1 U2 : R2 → (R2 → ℂ) × (R2 → ℂ))
    (hU1 : ∀ y ∈ Dplus f1, IsTSPSolution f1 kp k1 μ1 (incData f1 (pointSource kp y)).1
      (incData f1 (pointSource kp y)).2 (U1 y).1 (U1 y).2)
    (hU2 : ∀ y ∈ Dplus f2, IsTSPSolution f2 kp k2 μ2 (incData f2 (pointSource kp y)).1
      (incData f2 (pointSource kp y)).2 (U2 y).1 (U2 y).2)
    (hagree : ∀ x ∈ Dplus f1 ∩ Dplus f2, ∀ y ∈ Dplus f1 ∩ Dplus f2, (U1 y).1 x = (U2 y).1 x) :
    f1 = f2 ∧ μ1 = μ2 := by
  -- the interface is determined first (parts (i)–(ii), first half)
  have hf := interface_uniqueness f1 f2 hf1 hf2 lam1 lam2 hlam1 hlam2 hf1' hf2' kp k1 k2 μ1 μ2
    hpar1 hpar2 U1 U2 hU1 hU2 hagree
  subst hf
  -- with a common interface, the transmission coefficient is determined
  exact ⟨rfl, mu_uniqueness f1 hf1 lam1 hlam1 hf1' kp k1 k2 μ1 μ2 hpar1 hpar2 U1 U2 hU1 hU2
    (fun x hx y hy => hagree x ⟨hx, hx⟩ y ⟨hy, hy⟩)⟩
