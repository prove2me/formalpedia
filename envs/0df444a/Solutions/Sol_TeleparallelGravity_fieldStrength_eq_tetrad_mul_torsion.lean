-- Prove2me | solution 1 for TeleparallelGravity.fieldStrength_eq_tetrad_mul_torsion
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-26T17:02:32.721401+00:00
-- url     : https://prove2.me/submissions/5d3a136d-eb50-4f35-bde6-30320eba6b99

import Mathlib
import Definitions.Def_TeleparallelGravity_Defs

/-! e7a286aa TeleparallelGravity.fieldStrength_eq_tetrad_mul_torsion.
`Σ_ρ h^a_ρ T^ρ_{μν} = ∂_μ h^a_ν - ∂_ν h^a_μ` (contract `h · h⁻¹ = 1`); with
`h^a_μ = ∂_μ x^a + B^a_μ` the second partials of `x^a` commute, leaving `F^a_{μν}`. -/

set_option autoImplicit false

open scoped ContDiff

namespace TPGBuild

open TeleparallelGravity Matrix

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

theorem contract_tetrad (h : TetradField) (x : Spacetime) (hdet : (tetradMatrix h x).det ≠ 0)
    (T : Fin 4 → ℝ) (a : Fin 4) :
    ∑ ρ, h a ρ x * ∑ b, invTetrad h x ρ b * T b = T a := by
  have e : (tetradMatrix h x *ᵥ ((tetradMatrix h x)⁻¹ *ᵥ T)) a
      = ∑ ρ, h a ρ x * ∑ b, invTetrad h x ρ b * T b := rfl
  rw [← e, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdet),
    Matrix.one_mulVec]

theorem tetrad_mul_torsion (h : TetradField) (x : Spacetime)
    (hdet : (tetradMatrix h x).det ≠ 0) (a μ ν : Fin 4) :
    ∑ ρ, h a ρ x * torsion h ρ μ ν x = pd μ (h a ν) x - pd ν (h a μ) x := by
  have e := contract_tetrad h x hdet (fun b => pd μ (h b ν) x - pd ν (h b μ) x) a
  rw [← e]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  congr 1
  simp only [torsion, weitzenbock, ← Finset.sum_sub_distrib, mul_sub]

theorem fs_main (xa : Fin 4 → Spacetime → ℝ) (B : TetradField)
    (hxa : ∀ a, ContDiff ℝ ∞ (xa a)) (hB : ∀ a μ, ContDiff ℝ ∞ (B a μ))
    (hnd : ∀ x, (tetradMatrix (tetradOfPotential xa B) x).det ≠ 0)
    (a μ ν : Fin 4) (x : Spacetime) :
    fieldStrength B a μ ν x =
      ∑ ρ, tetradOfPotential xa B a ρ x * torsion (tetradOfPotential xa B) ρ μ ν x := by
  rw [tetrad_mul_torsion _ x (hnd x)]
  have e1 : ∀ b c, pd b (tetradOfPotential xa B a c) x
      = pd b (pd c (xa a)) x + pd b (B a c) x := fun b c =>
    pd_add (dAt (contDiff_pd (hxa a) c) x) (dAt (hB a c) x) b
  rw [e1, e1, pd_pd_comm (hxa a) ν μ x]
  simp only [fieldStrength]
  ring

end TPGBuild

open TeleparallelGravity in open scoped ContDiff in
theorem solution
    (xa : Fin 4 → Spacetime → ℝ) (B : TetradField)
    (hxa : ∀ a, ContDiff ℝ ∞ (xa a)) (hB : ∀ a μ, ContDiff ℝ ∞ (B a μ))
    (hnd : ∀ x, (tetradMatrix (tetradOfPotential xa B) x).det ≠ 0)
    (a μ ν : Fin 4) (x : Spacetime) :
    fieldStrength B a μ ν x =
      ∑ ρ, tetradOfPotential xa B a ρ x * torsion (tetradOfPotential xa B) ρ μ ν x := by
  exact TPGBuild.fs_main xa B hxa hB hnd a μ ν x
