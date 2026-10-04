-- Prove2me | solution 1 for RaritaSchwinger.massless_gamma_traceless_gauge
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T04:29:20.057609+00:00
-- url     : https://prove2.me/submissions/1d26bc50-a9be-4668-a7b6-0c87cea00fd1

import Mathlib
import Definitions.Def_RaritaSchwinger_core

set_option autoImplicit false

open DiracEquation

namespace RS82f9

open Matrix DiracEquation RaritaSchwinger

lemma eta_symm (a b : Fin 4) : eta a b = eta b a := by
  fin_cases a <;> fin_cases b <;> simp [eta]

lemma eta_sq (a : Fin 4) : eta a a * eta a a = 1 := by
  fin_cases a <;> simp [eta]

lemma eta_sum_left {V : Type} [AddCommGroup V] [Module ℂ V] (f : Fin 4 → V) (b : Fin 4) :
    ∑ a, eta a b • f a = eta b b • f b := by
  rw [Finset.sum_eq_single b]
  · intro a _ hab
    simp [eta, hab]
  · simp

lemma eta_sum_right {V : Type} [AddCommGroup V] [Module ℂ V] (f : Fin 4 → V) (b : Fin 4) :
    ∑ a, eta b a • f a = eta b b • f b := by
  simp_rw [eta_symm b]
  exact eta_sum_left f b

lemma anti (g : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (hg : IsGammaFamily g) (a b : Fin 4) :
    g a * g b = (2 * eta a b) • (1 : Matrix (Fin 4) (Fin 4) ℂ) - g b * g a :=
  eq_sub_of_add_eq (hg a b)

lemma gg (g : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (hg : IsGammaFamily g) (a : Fin 4) :
    g a * g a = eta a a • (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  have h := hg a a
  have h2 : (2 : ℂ) • (g a * g a) = (2 : ℂ) • (eta a a • (1 : Matrix (Fin 4) (Fin 4) ℂ)) := by
    rw [two_smul, h, smul_smul]
  exact smul_right_injective _ two_ne_zero h2

lemma gamma3_eq (g : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (hg : IsGammaFamily g) (μ ν ρ : Fin 4) :
    gamma3 g μ ν ρ = (1 / 2 : ℂ) • (g μ * g ν * g ρ - g ν * g μ * g ρ)
      + eta ρ μ • g ν - eta ρ ν • g μ := by
  have hA := anti g hg
  have T2 : g μ * g ρ * g ν = (2 * eta ρ ν) • g μ - g μ * g ν * g ρ := by
    rw [mul_assoc (g μ) (g ρ) (g ν), hA ρ ν, mul_sub, mul_smul_comm, mul_one,
      ← mul_assoc (g μ) (g ν) (g ρ)]
  have T4 : g ν * g ρ * g μ = (2 * eta ρ μ) • g ν - g ν * g μ * g ρ := by
    rw [mul_assoc (g ν) (g ρ) (g μ), hA ρ μ, mul_sub, mul_smul_comm, mul_one,
      ← mul_assoc (g ν) (g μ) (g ρ)]
  have T5 : g ρ * g μ * g ν = (2 * eta ρ μ) • g ν - (2 * eta ρ ν) • g μ + g μ * g ν * g ρ := by
    rw [hA ρ μ, sub_mul, smul_mul_assoc, one_mul, mul_assoc (g μ) (g ρ) (g ν), hA ρ ν, mul_sub,
      mul_smul_comm, mul_one, ← mul_assoc (g μ) (g ν) (g ρ)]
    abel
  have T6 : g ρ * g ν * g μ = (2 * eta ρ ν) • g μ - (2 * eta ρ μ) • g ν + g ν * g μ * g ρ := by
    rw [hA ρ ν, sub_mul, smul_mul_assoc, one_mul, mul_assoc (g ν) (g ρ) (g μ), hA ρ μ, mul_sub,
      mul_smul_comm, mul_one, ← mul_assoc (g ν) (g μ) (g ρ)]
    abel
  unfold gamma3
  rw [T2, T4, T5, T6]
  module

lemma alg (g : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (hg : IsGammaFamily g)
    (D : Fin 4 → Fin 4 → (Fin 4 → ℂ))
    (hG : ∀ ν, ∑ ρ, g ρ *ᵥ D ν ρ = 0)
    (hE : ∀ μ, ∑ ν, ∑ ρ, gamma3 g μ ν ρ *ᵥ D ν ρ = 0) :
    (∑ μ, eta μ μ • D μ μ = 0) ∧ ∀ μ, ∑ ν, g ν *ᵥ D ν μ = 0 := by
  set dv := ∑ μ, eta μ μ • D μ μ with hdv
  have P0 : ∀ A : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ, ∑ ν, ∑ ρ, (A ν * g ρ) *ᵥ D ν ρ = 0 := by
    intro A
    apply Finset.sum_eq_zero
    intro ν _
    simp_rw [← Matrix.mulVec_mulVec]
    rw [← Matrix.mulVec_sum, hG ν, Matrix.mulVec_zero]
  have key : ∀ μ, ∑ ν, ∑ ρ, gamma3 g μ ν ρ *ᵥ D ν ρ
      = eta μ μ • (∑ ν, g ν *ᵥ D ν μ) - g μ *ᵥ dv := by
    intro μ
    have e : ∀ ν ρ, gamma3 g μ ν ρ *ᵥ D ν ρ
        = (1 / 2 : ℂ) • ((g μ * g ν * g ρ) *ᵥ D ν ρ) - (1 / 2 : ℂ) • ((g ν * g μ * g ρ) *ᵥ D ν ρ)
          + eta ρ μ • (g ν *ᵥ D ν ρ) - eta ρ ν • (g μ *ᵥ D ν ρ) := by
      intro ν ρ
      rw [gamma3_eq g hg, Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.smul_mulVec,
        Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, smul_sub]
    have P1 : ∑ ν, ∑ ρ, (g μ * g ν * g ρ) *ᵥ D ν ρ = 0 := P0 (fun ν => g μ * g ν)
    have P2 : ∑ ν, ∑ ρ, (g ν * g μ * g ρ) *ᵥ D ν ρ = 0 := P0 (fun ν => g ν * g μ)
    have S3 : ∑ ν, ∑ ρ, eta ρ μ • (g ν *ᵥ D ν ρ) = eta μ μ • ∑ ν, g ν *ᵥ D ν μ := by
      rw [Finset.smul_sum]
      exact Finset.sum_congr rfl (fun ν _ => eta_sum_left (fun ρ => g ν *ᵥ D ν ρ) μ)
    have S4 : ∑ ν, ∑ ρ, eta ρ ν • (g μ *ᵥ D ν ρ) = g μ *ᵥ dv := by
      rw [hdv, Matrix.mulVec_sum]
      refine Finset.sum_congr rfl (fun ν _ => ?_)
      exact (eta_sum_left (fun ρ => g μ *ᵥ D ν ρ) ν).trans (Matrix.mulVec_smul _ _ _).symm
    calc ∑ ν, ∑ ρ, gamma3 g μ ν ρ *ᵥ D ν ρ
        = ∑ ν, ∑ ρ, ((1 / 2 : ℂ) • ((g μ * g ν * g ρ) *ᵥ D ν ρ)
            - (1 / 2 : ℂ) • ((g ν * g μ * g ρ) *ᵥ D ν ρ)
            + eta ρ μ • (g ν *ᵥ D ν ρ) - eta ρ ν • (g μ *ᵥ D ν ρ)) :=
          Finset.sum_congr rfl (fun ν _ => Finset.sum_congr rfl (fun ρ _ => e ν ρ))
      _ = (1 / 2 : ℂ) • (∑ ν, ∑ ρ, (g μ * g ν * g ρ) *ᵥ D ν ρ)
            - (1 / 2 : ℂ) • (∑ ν, ∑ ρ, (g ν * g μ * g ρ) *ᵥ D ν ρ)
            + ∑ ν, ∑ ρ, eta ρ μ • (g ν *ᵥ D ν ρ) - ∑ ν, ∑ ρ, eta ρ ν • (g μ *ᵥ D ν ρ) := by
          simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.smul_sum]
      _ = eta μ μ • (∑ ν, g ν *ᵥ D ν μ) - g μ *ᵥ dv := by
          rw [P1, P2, S3, S4]
          simp
  have hD : ∀ μ, ∑ ν, g ν *ᵥ D ν μ = eta μ μ • (g μ *ᵥ dv) := by
    intro μ
    have h := key μ
    rw [hE μ] at h
    have h2 : eta μ μ • ∑ ν, g ν *ᵥ D ν μ = g μ *ᵥ dv := sub_eq_zero.mp h.symm
    rw [← h2, smul_smul, eta_sq, one_smul]
  -- contract with γ^μ
  have L1 : ∑ μ, g μ *ᵥ (∑ ν, g ν *ᵥ D ν μ) = (2 : ℂ) • dv := by
    have step : ∀ μ, g μ *ᵥ (∑ ν, g ν *ᵥ D ν μ)
        = (2 : ℂ) • (∑ ν, eta μ ν • D ν μ) - ∑ ν, (g ν * g μ) *ᵥ D ν μ := by
      intro μ
      rw [Matrix.mulVec_sum, Finset.smul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun ν _ => ?_)
      rw [Matrix.mulVec_mulVec, anti g hg μ ν, Matrix.sub_mulVec, Matrix.smul_mulVec,
        Matrix.one_mulVec, mul_smul]
    rw [Finset.sum_congr rfl (fun μ _ => step μ), Finset.sum_sub_distrib, Finset.sum_comm (f := fun μ ν => (g ν * g μ) *ᵥ D ν μ)]
    rw [P0 (fun ν => g ν), sub_zero, ← Finset.smul_sum, hdv]
    congr 1
    exact Finset.sum_congr rfl (fun μ _ => eta_sum_right (fun ν => D ν μ) μ)
  have L2 : ∑ μ, g μ *ᵥ (∑ ν, g ν *ᵥ D ν μ) = (4 : ℂ) • dv := by
    simp_rw [hD, Matrix.mulVec_smul, Matrix.mulVec_mulVec, gg g hg, Matrix.smul_mulVec,
      Matrix.one_mulVec, smul_smul, eta_sq, one_smul]
    rw [Fin.sum_univ_four]
    module
  have h3 : (2 : ℂ) • dv = 0 := by
    have h := L1.symm.trans L2
    rw [show (2 : ℂ) • dv = (4 : ℂ) • dv - (2 : ℂ) • dv by module, ← h, sub_self]
  have hdv0 : dv = 0 := (smul_eq_zero.mp h3).resolve_left two_ne_zero
  refine ⟨hdv0, fun μ => ?_⟩
  rw [hD, hdv0, Matrix.mulVec_zero, smul_zero]

lemma gauge_deriv (g : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (psi : VectorSpinorField)
    (hpsi : ContDiff ℝ 1 psi) (hgauge : ∀ x, gammaTrace g psi x = 0) (x : Fin 4 → ℝ)
    (ν : Fin 4) : ∑ ρ, g ρ *ᵥ pd (comp psi ρ) ν x = 0 := by
  have hd : Differentiable ℝ psi := hpsi.differentiable one_ne_zero
  have hc : ∀ ρ, HasFDerivAt (comp psi ρ) (fderiv ℝ (comp psi ρ) x) x := fun ρ =>
    (differentiableAt_pi.1 (hd x) ρ).hasFDerivAt
  let L : Fin 4 → (Fin 4 → ℂ) →L[ℝ] (Fin 4 → ℂ) := fun ρ =>
    LinearMap.toContinuousLinearMap ((Matrix.mulVecLin (g ρ)).restrictScalars ℝ)
  have hsum : HasFDerivAt (gammaTrace g psi)
      (∑ ρ, (L ρ).comp (fderiv ℝ (comp psi ρ) x)) x := by
    refine (HasFDerivAt.sum (u := Finset.univ)
      (fun ρ _ => (L ρ).hasFDerivAt.comp x (hc ρ))).congr_of_eventuallyEq ?_
    refine Filter.Eventually.of_forall (fun y => ?_)
    simp [gammaTrace, L, RaritaSchwinger.comp, Finset.sum_apply]
  have h0 : HasFDerivAt (gammaTrace g psi) (0 : (Fin 4 → ℝ) →L[ℝ] (Fin 4 → ℂ)) x := by
    have : gammaTrace g psi = fun _ => 0 := funext hgauge
    rw [this]
    exact hasFDerivAt_const 0 x
  have := congrArg (fun T => T (Pi.single ν 1)) (hsum.unique h0)
  simpa [L, pd] using this

end RS82f9

open DiracEquation RaritaSchwinger in
theorem solution (g : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ)
    (hg : IsGammaFamily g) (psi : VectorSpinorField) (hpsi : ContDiff ℝ 1 psi)
    (hEq : IsMasslessRSSolution g psi) (hgauge : ∀ x, gammaTrace g psi x = 0) :
    ∀ x, (∀ mu, diracOperator g psi mu x = 0) ∧ divergence psi x = 0 ∧
      gammaTrace g psi x = 0 := by
  intro x
  obtain ⟨h1, h2⟩ := RS82f9.alg g hg (fun ν ρ => pd (comp psi ρ) ν x)
    (fun ν => RS82f9.gauge_deriv g psi hpsi hgauge x ν) (fun μ => hEq x μ)
  exact ⟨fun mu => h2 mu, h1, hgauge x⟩
