-- Prove2me | solution 1 for RaritaSchwinger.massless_gauge_invariance
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T04:50:12.322604+00:00
-- url     : https://prove2.me/submissions/2c5999c1-3649-435e-9d4a-ed796c4134ea

import Mathlib
import Definitions.Def_RaritaSchwinger_core

open DiracEquation

namespace RS26e8bf97

open Matrix DiracEquation RaritaSchwinger

lemma gamma3_swap (g : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (mu nu rho : Fin 4) :
    gamma3 g mu rho nu = - gamma3 g mu nu rho := by
  unfold gamma3
  rw [← smul_neg]
  congr 1
  abel

lemma pd2_symm (eps : (Fin 4 → ℝ) → (Fin 4 → ℂ)) (heps : ContDiff ℝ 2 eps)
    (x : Fin 4 → ℝ) (nu rho : Fin 4) :
    pd (pd eps rho) nu x = pd (pd eps nu) rho x := by
  have hd : Differentiable ℝ (fderiv ℝ eps) :=
    (heps.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have key : ∀ a b : Fin 4, pd (pd eps a) b x
      = fderiv ℝ (fderiv ℝ eps) x (Pi.single b 1) (Pi.single a 1) := by
    intro a b
    unfold pd
    have h3 := ((ContinuousLinearMap.apply ℝ (Fin 4 → ℂ) (Pi.single a (1:ℝ))).hasFDerivAt
      (x := fderiv ℝ eps x)).comp x (hd x).hasFDerivAt
    have h4 : fderiv ℝ (fun y => fderiv ℝ eps y (Pi.single a 1)) x = _ := h3.fderiv
    rw [h4]
    rfl
  have hsym : IsSymmSndFDerivAt ℝ eps x :=
    (heps.contDiffAt).isSymmSndFDerivAt (by simp [minSmoothness_of_isRCLikeNormedField])
  rw [key, key, hsym.eq]

end RS26e8bf97

open DiracEquation RaritaSchwinger in
theorem solution (g : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (hg : IsGammaFamily g)
    (psi : VectorSpinorField) (hpsi : ContDiff ℝ 1 psi)
    (eps : (Fin 4 → ℝ) → (Fin 4 → ℂ)) (heps : ContDiff ℝ 2 eps) :
    IsMasslessRSSolution g (fun x mu => psi x mu + pd eps mu x) ↔
      IsMasslessRSSolution g psi := by
  have hpd : ∀ rho, Differentiable ℝ (pd eps rho) := by
    intro rho
    have h1 : ContDiff ℝ 1 (fderiv ℝ eps) := heps.fderiv_right (m := 1) (by norm_num)
    have h2 : ContDiff ℝ 1 (fun y => fderiv ℝ eps y (Pi.single rho 1)) :=
      h1.clm_apply contDiff_const
    exact h2.differentiable (by norm_num)
  have hc : ∀ rho, Differentiable ℝ (comp psi rho) := by
    intro rho y
    have := (hpsi.differentiable (by norm_num)) y
    exact differentiableAt_pi.1 this rho
  have hsplit : ∀ (x : Fin 4 → ℝ) (nu rho : Fin 4),
      pd (comp (fun (x : Fin 4 → ℝ) (mu : Fin 4) => psi x mu + pd eps mu x) rho) nu x
        = pd (comp psi rho) nu x + pd (pd eps rho) nu x := by
    intro x nu rho
    show fderiv ℝ (fun y => comp psi rho y + pd eps rho y) x (Pi.single nu 1) = _
    have h5 : fderiv ℝ (fun y => comp psi rho y + pd eps rho y) x = _ :=
      ((hc rho x).hasFDerivAt.add (hpd rho x).hasFDerivAt).fderiv
    rw [h5]
    rfl
  have hzero : ∀ x mu, ∑ nu, ∑ rho,
      (gamma3 g mu nu rho).mulVec (pd (pd eps rho) nu x) = 0 := by
    intro x mu
    set S := ∑ nu, ∑ rho, (gamma3 g mu nu rho).mulVec (pd (pd eps rho) nu x) with hS
    have h2 : S = -S := by
      conv_rhs => rw [hS, Finset.sum_comm]
      rw [hS, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun nu _ => ?_
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun rho _ => ?_
      rw [RS26e8bf97.gamma3_swap g mu rho nu, RS26e8bf97.pd2_symm eps heps x nu rho,
        Matrix.neg_mulVec]
    have : (2:ℂ) • S = 0 := by
      rw [two_smul]; nth_rewrite 2 [h2]; simp
    exact (smul_eq_zero.1 this).resolve_left (by norm_num)
  have heq : ∀ x mu, ∑ nu, ∑ rho, (gamma3 g mu nu rho).mulVec
        (pd (comp (fun (x : Fin 4 → ℝ) (mu : Fin 4) => psi x mu + pd eps mu x) rho) nu x)
      = ∑ nu, ∑ rho, (gamma3 g mu nu rho).mulVec (pd (comp psi rho) nu x) := by
    intro x mu
    simp_rw [hsplit x, Matrix.mulVec_add, Finset.sum_add_distrib]
    rw [hzero x mu, add_zero]
  unfold IsMasslessRSSolution
  simp only [heq]
