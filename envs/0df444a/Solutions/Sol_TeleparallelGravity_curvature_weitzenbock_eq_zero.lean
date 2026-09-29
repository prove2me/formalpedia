-- Prove2me | solution 1 for TeleparallelGravity.curvature_weitzenbock_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-26T18:03:48.188862+00:00
-- url     : https://prove2.me/submissions/d51741d4-2359-459a-b528-e8b3e94449db

import Mathlib
import Definitions.Def_TeleparallelGravity_Defs

/-! 9cc7e483 TeleparallelGravity.curvature_weitzenbock_eq_zero.
`h⁻¹` is smooth (`det⁻¹ • adj`, `det h ≠ 0`); differentiating `h⁻¹ h = 1` gives
`∂_μ (h⁻¹)^ρ_a = -Σ_σ Γ^ρ_{σμ} (h⁻¹)^σ_a`. Hence
`∂_μ Γ^ρ_{θν} = -Σ_σ Γ^ρ_{σμ} Γ^σ_{θν} + h_a^ρ ∂_μ∂_ν h^a_θ`; the second-derivative terms
cancel by symmetry of second partials and the quadratic terms cancel the rest. -/

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

theorem pd_mul {f g : Spacetime → ℝ} {x : Spacetime} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) (i : Fin 4) :
    pd i (fun y => f y * g y) x = pd i f x * g x + f x * pd i g x := by
  simp [pd, fderiv_fun_mul hf hg]
  ring

theorem pd_sum {F : Fin 4 → Spacetime → ℝ} {x : Spacetime}
    (h : ∀ k, DifferentiableAt ℝ (F k) x) (i : Fin 4) :
    pd i (fun y => ∑ k, F k y) x = ∑ k, pd i (F k) x := by
  simp [pd, fderiv_fun_sum (fun k _ => h k)]

theorem pd_const (c : ℝ) (i : Fin 4) (x : Spacetime) : pd i (fun _ => c) x = 0 := by
  simp [pd]

theorem contDiff_det {M : Spacetime → Matrix (Fin 4) (Fin 4) ℝ}
    (h : ∀ i j, ContDiff ℝ ∞ (fun x => M x i j)) :
    ContDiff ℝ ∞ (fun x => (M x).det) := by
  simp_rw [Matrix.det_apply']
  exact ContDiff.sum fun σ _ => contDiff_const.mul (contDiff_prod fun i _ => h _ _)

theorem contDiff_invTetrad (h : TetradField) (hh : IsTetrad h) (i j : Fin 4) :
    ContDiff ℝ ∞ (fun x => invTetrad h x i j) := by
  have hg : ∀ a b, ContDiff ℝ ∞ (fun x => tetradMatrix h x a b) := fun a b => hh.smooth a b
  have hdet : ContDiff ℝ ∞ (fun x => (tetradMatrix h x).det) := contDiff_det hg
  have hadj : ContDiff ℝ ∞ (fun x => (tetradMatrix h x).adjugate i j) := by
    simp_rw [Matrix.adjugate_apply]
    apply contDiff_det
    intro a b
    by_cases hab : a = j
    · subst hab; simp only [Matrix.updateRow_self]; exact contDiff_const
    · simp only [Matrix.updateRow_ne hab]; exact hg a b
  have e : (fun x => invTetrad h x i j)
      = fun x => ((tetradMatrix h x).det)⁻¹ * (tetradMatrix h x).adjugate i j := by
    funext x
    simp [invTetrad, Matrix.inv_def, Ring.inverse_eq_inv]
  rw [e]
  exact (hdet.inv (fun x => hh.nondegenerate x)).mul hadj

theorem pd_inv (h : TetradField) (hh : IsTetrad h) (μ ρ a : Fin 4) (x : Spacetime) :
    pd μ (fun y => invTetrad h y ρ a) x
      = -∑ σ, (∑ b, invTetrad h x ρ b * pd μ (h b σ) x) * invTetrad h x σ a := by
  have hu : ∀ y, IsUnit (tetradMatrix h y).det :=
    fun y => isUnit_iff_ne_zero.mpr (hh.nondegenerate y)
  have hcon : ∀ D : Fin 4 → ℝ, ∑ σ, (∑ b, D b * h b σ x) * invTetrad h x σ a = D a := by
    intro D
    have e : ((D ᵥ* tetradMatrix h x) ᵥ* invTetrad h x) a
        = ∑ σ, (∑ b, D b * h b σ x) * invTetrad h x σ a := rfl
    rw [← e, Matrix.vecMul_vecMul, invTetrad, Matrix.mul_nonsing_inv _ (hu x), Matrix.vecMul_one]
  have hD : ∀ σ, ∑ b, pd μ (fun y => invTetrad h y ρ b) x * h b σ x
      = -∑ b, invTetrad h x ρ b * pd μ (h b σ) x := by
    intro σ
    have hconst : (fun y => ∑ b, invTetrad h y ρ b * h b σ y)
        = fun _ => (1 : Matrix (Fin 4) (Fin 4) ℝ) ρ σ := by
      funext y
      have e : ∑ b, invTetrad h y ρ b * h b σ y = (invTetrad h y * tetradMatrix h y) ρ σ := rfl
      rw [e, invTetrad, Matrix.nonsing_inv_mul _ (hu y)]
    have h0 := pd_const ((1 : Matrix (Fin 4) (Fin 4) ℝ) ρ σ) μ x
    rw [← hconst, pd_sum (F := fun b y => invTetrad h y ρ b * h b σ y)
      (fun b => dAt ((contDiff_invTetrad h hh ρ b).mul (hh.smooth b σ)) x)] at h0
    have h1 : ∀ b, pd μ (fun y => invTetrad h y ρ b * h b σ y) x
        = pd μ (fun y => invTetrad h y ρ b) x * h b σ x + invTetrad h x ρ b * pd μ (h b σ) x :=
      fun b => pd_mul (dAt (contDiff_invTetrad h hh ρ b) x) (dAt (hh.smooth b σ) x) μ
    simp only [h1, Finset.sum_add_distrib] at h0
    linarith
  rw [← hcon (fun b => pd μ (fun y => invTetrad h y ρ b) x), ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [hD σ]
  ring

theorem curv_alg (h : TetradField) (x : Spacetime) (ρ θ μ ν : Fin 4) :
    ∑ a, (-∑ σ, (∑ b, invTetrad h x ρ b * pd μ (h b σ) x) * invTetrad h x σ a)
        * pd ν (h a θ) x
      - ∑ a, (-∑ σ, (∑ b, invTetrad h x ρ b * pd ν (h b σ) x) * invTetrad h x σ a)
        * pd μ (h a θ) x
      + ∑ σ, ((∑ b, invTetrad h x ρ b * pd μ (h b σ) x)
          * (∑ a, invTetrad h x σ a * pd ν (h a θ) x)
        - (∑ b, invTetrad h x ρ b * pd ν (h b σ) x)
          * (∑ a, invTetrad h x σ a * pd μ (h a θ) x)) = 0 := by
  simp only [Fin.sum_univ_four]
  ring

theorem curv_main (h : TetradField) (hh : IsTetrad h) (ρ θ μ ν : Fin 4) (x : Spacetime) :
    curvature (weitzenbock h) ρ θ μ ν x = 0 := by
  have hdW : ∀ μ ν, pd μ (weitzenbock h ρ θ ν) x
      = ∑ a, (-∑ σ, (∑ b, invTetrad h x ρ b * pd μ (h b σ) x) * invTetrad h x σ a)
          * pd ν (h a θ) x
        + ∑ a, invTetrad h x ρ a * pd μ (pd ν (h a θ)) x := by
    intro μ ν
    have e : weitzenbock h ρ θ ν = fun y => ∑ a, invTetrad h y ρ a * pd ν (h a θ) y := rfl
    rw [e, pd_sum (F := fun a y => invTetrad h y ρ a * pd ν (h a θ) y)
      (fun a => dAt ((contDiff_invTetrad h hh ρ a).mul (contDiff_pd (hh.smooth a θ) ν)) x),
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [pd_mul (dAt (contDiff_invTetrad h hh ρ a) x) (dAt (contDiff_pd (hh.smooth a θ) ν) x),
      pd_inv h hh μ ρ a x]
  have hsym : ∑ a, invTetrad h x ρ a * pd μ (pd ν (h a θ)) x
      = ∑ a, invTetrad h x ρ a * pd ν (pd μ (h a θ)) x :=
    Finset.sum_congr rfl fun a _ => by rw [pd_pd_comm (hh.smooth a θ) ν μ x]
  have hW : ∀ ρ' σ' μ', weitzenbock h ρ' σ' μ' x
      = ∑ b, invTetrad h x ρ' b * pd μ' (h b σ') x := fun _ _ _ => rfl
  unfold curvature
  rw [hdW μ ν, hdW ν μ]
  simp only [hW]
  rw [hsym]
  linear_combination curv_alg h x ρ θ μ ν

end TPGBuild

open TeleparallelGravity in open scoped ContDiff in
theorem solution (h : TetradField) (hh : IsTetrad h)
    (ρ θ μ ν : Fin 4) (x : Spacetime) :
    curvature (weitzenbock h) ρ θ μ ν x = 0 := by
  exact TPGBuild.curv_main h hh ρ θ μ ν x
