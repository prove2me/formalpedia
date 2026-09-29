-- Prove2me | solution 1 for TeleparallelGravity.tetrad_and_fieldStrength_gauge_invariant
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-26T16:55:06.789527+00:00
-- url     : https://prove2.me/submissions/d5930f2d-0949-4499-9004-b4d39d0d9b58

import Mathlib
import Definitions.Def_TeleparallelGravity_Defs

/-! 1ef5e9bc TeleparallelGravity.tetrad_and_fieldStrength_gauge_invariant.
`pd` is linear on differentiable functions, `pd` of a smooth function is smooth, and second
coordinate partials of a smooth function commute. -/

set_option autoImplicit false

open scoped ContDiff

namespace TPGBuild

open TeleparallelGravity

theorem pd_add {f g : Spacetime → ℝ} {x : Spacetime} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) (i : Fin 4) :
    pd i (fun y => f y + g y) x = pd i f x + pd i g x := by
  simp [pd, fderiv_fun_add hf hg]

theorem pd_sub {f g : Spacetime → ℝ} {x : Spacetime} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) (i : Fin 4) :
    pd i (fun y => f y - g y) x = pd i f x - pd i g x := by
  simp [pd, fderiv_fun_sub hf hg]

theorem contDiff_pd {f : Spacetime → ℝ} (hf : ContDiff ℝ ∞ f) (i : Fin 4) :
    ContDiff ℝ ∞ (pd i f) := by
  unfold pd
  exact (hf.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

theorem two_le_infty : (2 : WithTop ℕ∞) ≤ ∞ := WithTop.coe_le_coe.mpr le_top

theorem dAt {f : Spacetime → ℝ} (hf : ContDiff ℝ ∞ f) (x : Spacetime) :
    DifferentiableAt ℝ f x :=
  (hf.differentiable (by simp)) x

theorem pd_pd_comm {f : Spacetime → ℝ} (hf : ContDiff ℝ ∞ f) (a b : Fin 4) (x : Spacetime) :
    pd b (pd a f) x = pd a (pd b f) x := by
  have hs : IsSymmSndFDerivAt ℝ f x :=
    hf.contDiffAt.isSymmSndFDerivAt (by simpa using two_le_infty)
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    ((hf.fderiv_right (m := ∞) (by simp)).differentiable (by simp)).differentiableAt
  unfold pd
  rw [fderiv_clm_apply hd (differentiableAt_const _),
    fderiv_clm_apply hd (differentiableAt_const _)]
  simp
  exact hs _ _

theorem gauge (xa ε : Fin 4 → Spacetime → ℝ) (B : TetradField)
    (hxa : ∀ a, ContDiff ℝ ∞ (xa a)) (hε : ∀ a, ContDiff ℝ ∞ (ε a))
    (hB : ∀ a μ, ContDiff ℝ ∞ (B a μ)) :
    tetradOfPotential (fun a y => xa a y + ε a y) (fun a μ y => B a μ y - pd μ (ε a) y)
        = tetradOfPotential xa B ∧
      fieldStrength (fun a μ y => B a μ y - pd μ (ε a) y) = fieldStrength B := by
  constructor
  · funext a μ y
    simp only [tetradOfPotential]
    rw [pd_add (dAt (hxa a) y) (dAt (hε a) y)]
    ring
  · funext a μ ν x
    simp only [fieldStrength]
    rw [pd_sub (dAt (hB a ν) x) (dAt (contDiff_pd (hε a) ν) x),
      pd_sub (dAt (hB a μ) x) (dAt (contDiff_pd (hε a) μ) x),
      pd_pd_comm (hε a) ν μ x]
    ring

end TPGBuild

open TeleparallelGravity in open scoped ContDiff in
theorem solution
    (xa ε : Fin 4 → Spacetime → ℝ) (B : TetradField)
    (hxa : ∀ a, ContDiff ℝ ∞ (xa a)) (hε : ∀ a, ContDiff ℝ ∞ (ε a))
    (hB : ∀ a μ, ContDiff ℝ ∞ (B a μ)) :
    tetradOfPotential (fun a y => xa a y + ε a y) (fun a μ y => B a μ y - pd μ (ε a) y)
        = tetradOfPotential xa B ∧
      fieldStrength (fun a μ y => B a μ y - pd μ (ε a) y) = fieldStrength B := by
  exact TPGBuild.gauge xa ε B hxa hε hB
