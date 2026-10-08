-- Prove2me | solution 1 for PolyakovAction.conformal_gauge_wave_equation
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T12:01:00.576763+00:00
-- url     : https://prove2.me/submissions/927c418e-726e-4d10-a2ba-a547449bcd7e

import Mathlib
import Definitions.Def_PolyakovAction_Defs

set_option autoImplicit false

open MeasureTheory Filter Asymptotics
open scoped Matrix Topology

namespace PolyakovAction

lemma eta2_mul_self_e86bf5ba : minkowskiMetric 2 * minkowskiMetric 2 = 1 := by
  unfold minkowskiMetric
  rw [Matrix.diagonal_mul_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

lemma eta2_inv_e86bf5ba : (minkowskiMetric 2)⁻¹ = minkowskiMetric 2 :=
  Matrix.inv_eq_left_inv eta2_mul_self_e86bf5ba

lemma eta2_det_e86bf5ba : (minkowskiMetric 2).det = -1 := by
  unfold minkowskiMetric
  rw [Matrix.det_diagonal, Fin.prod_univ_two]
  norm_num

lemma lagr2_e86bf5ba {D : ℕ} (g : Spacetime D → Matrix (Fin D) (Fin D) ℝ)
    (X : Worldsheet → Spacetime D) (σ : Worldsheet) :
    polyakovLagrangian g (fun _ => minkowskiMetric 2) X σ
      = inducedMetric g X σ 0 0 - inducedMetric g X σ 1 1 := by
  unfold polyakovLagrangian
  rw [eta2_inv_e86bf5ba, eta2_det_e86bf5ba]
  simp only [neg_neg, Real.sqrt_one, one_mul, Fin.sum_univ_two]
  simp [minkowskiMetric, Matrix.diagonal_apply]
  ring

lemma im_eta_e86bf5ba {D : ℕ} (Y : Worldsheet → Spacetime D) (σ : Worldsheet) (a b : Fin 2) :
    inducedMetric (fun _ => minkowskiMetric D) Y σ a b
      = ∑ μ, (if μ.val = 0 then (1:ℝ) else -1) * partialDeriv Y a μ σ * partialDeriv Y b μ σ := by
  unfold inducedMetric
  rw [Matrix.of_apply]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [Finset.sum_eq_single μ]
  · simp only [minkowskiMetric, Matrix.diagonal_apply_eq]
  · intro ν _ hν
    simp only [minkowskiMetric, Matrix.diagonal_apply_ne _ (Ne.symm hν), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ μ) h

lemma lagr_eta_e86bf5ba {D : ℕ} (Y : Worldsheet → Spacetime D) (σ : Worldsheet) :
    polyakovLagrangian (fun _ => minkowskiMetric D) (fun _ => minkowskiMetric 2) Y σ
      = ∑ μ, (if μ.val = 0 then (1:ℝ) else -1) *
          (partialDeriv Y 0 μ σ * partialDeriv Y 0 μ σ
            - partialDeriv Y 1 μ σ * partialDeriv Y 1 μ σ) := by
  rw [lagr2_e86bf5ba, im_eta_e86bf5ba, im_eta_e86bf5ba, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun μ _ => ?_
  ring

lemma pd_pert_e86bf5ba {D : ℕ} (X : Worldsheet → Spacetime D) (φ : Worldsheet → ℝ)
    (hX : Differentiable ℝ X) (hφ : Differentiable ℝ φ) (μ0 : Fin D) (ε : ℝ)
    (a : Fin 2) (μ : Fin D) (σ : Worldsheet) :
    partialDeriv (fun σ' => X σ' + ε • (φ σ' • (Pi.single μ0 (1:ℝ) : Spacetime D))) a μ σ
      = partialDeriv X a μ σ
        + ε * (fderiv ℝ φ σ (Pi.single a 1) * (Pi.single μ0 (1:ℝ) : Spacetime D) μ) := by
  have h1 : HasFDerivAt (fun σ' => X σ' + ε • (φ σ' • (Pi.single μ0 (1:ℝ) : Spacetime D)))
      (fderiv ℝ X σ + ε • (fderiv ℝ φ σ).smulRight (Pi.single μ0 (1:ℝ) : Spacetime D)) σ :=
    (hX σ).hasFDerivAt.add (((hφ σ).hasFDerivAt.smul_const _).const_smul ε)
  unfold partialDeriv
  rw [h1.fderiv]
  simp [smul_eq_mul]

lemma diff_e86bf5ba {D : ℕ} (X : Worldsheet → Spacetime D) (φ : Worldsheet → ℝ)
    (hX : Differentiable ℝ X) (hφ : Differentiable ℝ φ) (μ0 : Fin D) (ε : ℝ)
    (σ : Worldsheet) :
    polyakovLagrangian (fun _ => minkowskiMetric D) (fun _ => minkowskiMetric 2)
        (fun σ' => X σ' + ε • (φ σ' • (Pi.single μ0 (1:ℝ) : Spacetime D))) σ
      - polyakovLagrangian (fun _ => minkowskiMetric D) (fun _ => minkowskiMetric 2) X σ
      = ε * ((if μ0.val = 0 then (1:ℝ) else -1) *
            (2 * (partialDeriv X 0 μ0 σ * fderiv ℝ φ σ (Pi.single 0 1)
              - partialDeriv X 1 μ0 σ * fderiv ℝ φ σ (Pi.single 1 1))))
        + ε ^ 2 * ((if μ0.val = 0 then (1:ℝ) else -1) *
            (fderiv ℝ φ σ (Pi.single 0 1) * fderiv ℝ φ σ (Pi.single 0 1)
              - fderiv ℝ φ σ (Pi.single 1 1) * fderiv ℝ φ σ (Pi.single 1 1))) := by
  rw [lagr_eta_e86bf5ba, lagr_eta_e86bf5ba, ← Finset.sum_sub_distrib]
  rw [Finset.sum_eq_single μ0]
  · simp only [pd_pert_e86bf5ba X φ hX hφ, Pi.single_eq_same]
    ring
  · intro μ _ hμ
    simp only [pd_pert_e86bf5ba X φ hX hφ, Pi.single_eq_of_ne hμ]
    ring
  · simp

end PolyakovAction

open PolyakovAction in
theorem solution {D : ℕ} (T : ℝ) (hT : T ≠ 0)
    (X : Worldsheet → Spacetime D) (hX : ContDiff ℝ 2 X)
    (hvar : ∀ δX : Worldsheet → Spacetime D, ContDiff ℝ (⊤ : ℕ∞) δX → HasCompactSupport δX →
      HasDerivAt
        (fun ε : ℝ => T / 2 * ∫ σ,
          (polyakovLagrangian (fun _ => minkowskiMetric D) (fun _ => minkowskiMetric 2)
              (fun σ' => X σ' + ε • δX σ') σ
            - polyakovLagrangian (fun _ => minkowskiMetric D) (fun _ => minkowskiMetric 2) X σ))
        0 0) :
    ∀ σ : Worldsheet, ∀ μ : Fin D,
      secondPartialDeriv X 0 0 μ σ - secondPartialDeriv X 1 1 μ σ = 0 := by
  intro σ0 μ0
  have hXd : Differentiable ℝ X := hX.differentiable (by norm_num)
  have hfX : ContDiff ℝ 1 (fderiv ℝ X) := hX.fderiv_right (by norm_num)
  have hP : ∀ a : Fin 2, ContDiff ℝ 1 (fun σ => partialDeriv X a μ0 σ) := by
    intro a
    unfold partialDeriv
    exact (contDiff_apply ℝ ℝ μ0).comp (hfX.clm_apply contDiff_const)
  have hbridge : ∀ a : Fin 2, ∀ σ : Worldsheet,
      fderiv ℝ (fun σ => partialDeriv X a μ0 σ) σ (Pi.single a 1)
        = secondPartialDeriv X a a μ0 σ := by
    intro a σ
    have hg : Differentiable ℝ (fun σ' => fderiv ℝ X σ' (Pi.single a 1)) :=
      (hfX.clm_apply contDiff_const).differentiable (by norm_num)
    have h2 := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin D => ℝ) μ0).hasFDerivAt.comp
      σ (hg σ).hasFDerivAt
    unfold partialDeriv secondPartialDeriv
    rw [show (fun σ => fderiv ℝ X σ (Pi.single a 1) μ0)
        = (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin D => ℝ) μ0) ∘
          (fun σ' => fderiv ℝ X σ' (Pi.single a 1)) from rfl, h2.fderiv]
    rfl
  have hS : ∀ a : Fin 2, Continuous (fun σ => secondPartialDeriv X a a μ0 σ) := by
    intro a
    have : (fun σ => secondPartialDeriv X a a μ0 σ)
        = fun σ => fderiv ℝ (fun σ => partialDeriv X a μ0 σ) σ (Pi.single a 1) :=
      funext fun σ => (hbridge a σ).symm
    rw [this]
    exact ((hP a).continuous_fderiv (by norm_num)).clm_apply continuous_const
  set W : Worldsheet → ℝ :=
    fun σ => secondPartialDeriv X 0 0 μ0 σ - secondPartialDeriv X 1 1 μ0 σ with hW
  have hWc : Continuous W := (hS 0).sub (hS 1)
  have key : ∀ φ : Worldsheet → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      ∫ σ, φ σ • W σ = 0 := by
    intro φ hφ hφc
    have hφd : Differentiable ℝ φ := hφ.differentiable (by simp)
    set η : ℝ := if μ0.val = 0 then 1 else -1 with hη
    have hη0 : η ≠ 0 := by rw [hη]; split_ifs <;> norm_num
    have hdφc : ∀ a : Fin 2, Continuous (fun σ => fderiv ℝ φ σ (Pi.single a 1)) :=
      fun a => (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
    have hdφs : ∀ a : Fin 2, HasCompactSupport (fun σ => fderiv ℝ φ σ (Pi.single a 1)) :=
      fun a => hφc.fderiv_apply (𝕜 := ℝ) _
    have hPdφ : ∀ a : Fin 2,
        Integrable (fun σ => partialDeriv X a μ0 σ * fderiv ℝ φ σ (Pi.single a 1)) := fun a =>
      ((hP a).continuous.mul (hdφc a)).integrable_of_hasCompactSupport (hdφs a).mul_left
    have hdd : ∀ a : Fin 2,
        Integrable (fun σ => fderiv ℝ φ σ (Pi.single a 1) * fderiv ℝ φ σ (Pi.single a 1)) :=
      fun a => ((hdφc a).mul (hdφc a)).integrable_of_hasCompactSupport (hdφs a).mul_left
    have hSφ : ∀ a : Fin 2, Integrable (fun σ => secondPartialDeriv X a a μ0 σ * φ σ) :=
      fun a => ((hS a).mul hφ.continuous).integrable_of_hasCompactSupport hφc.mul_left
    obtain ⟨A, hA⟩ : ∃ A : Worldsheet → ℝ, A = fun σ => η * (2 * (partialDeriv X 0 μ0 σ *
      fderiv ℝ φ σ (Pi.single 0 1) - partialDeriv X 1 μ0 σ * fderiv ℝ φ σ (Pi.single 1 1))) :=
      ⟨_, rfl⟩
    obtain ⟨B, hB⟩ : ∃ B : Worldsheet → ℝ, B = fun σ => η * (fderiv ℝ φ σ (Pi.single 0 1) *
      fderiv ℝ φ σ (Pi.single 0 1) - fderiv ℝ φ σ (Pi.single 1 1) * fderiv ℝ φ σ (Pi.single 1 1)) :=
      ⟨_, rfl⟩
    have hAi : Integrable A := by
      rw [hA]; exact (((hPdφ 0).sub (hPdφ 1)).const_mul 2).const_mul η
    have hBi : Integrable B := by
      rw [hB]; exact ((hdd 0).sub (hdd 1)).const_mul η
    have hint : ∀ ε : ℝ, ∫ σ, (polyakovLagrangian (fun _ => minkowskiMetric D)
          (fun _ => minkowskiMetric 2)
          (fun σ' => X σ' + ε • (φ σ' • (Pi.single μ0 (1:ℝ) : Spacetime D))) σ
        - polyakovLagrangian (fun _ => minkowskiMetric D) (fun _ => minkowskiMetric 2) X σ)
        = ε * (∫ σ, A σ) + ε ^ 2 * ∫ σ, B σ := by
      intro ε
      have hfun : (fun σ => polyakovLagrangian (fun _ => minkowskiMetric D)
          (fun _ => minkowskiMetric 2)
          (fun σ' => X σ' + ε • (φ σ' • (Pi.single μ0 (1:ℝ) : Spacetime D))) σ
          - polyakovLagrangian (fun _ => minkowskiMetric D) (fun _ => minkowskiMetric 2) X σ)
          = fun σ => ε * A σ + ε ^ 2 * B σ :=
        funext fun σ => by rw [hA, hB]; exact diff_e86bf5ba X φ hXd hφd μ0 ε σ
      rw [hfun, integral_add (hAi.const_mul ε) (hBi.const_mul _), integral_const_mul ε,
        integral_const_mul (ε ^ 2)]
    have hd := hvar (fun σ => φ σ • (Pi.single μ0 (1:ℝ) : Spacetime D))
      (hφ.smul contDiff_const) (hφc.smul_right)
    have hd' : HasDerivAt (fun ε : ℝ => T / 2 * (ε * (∫ σ, A σ) + ε ^ 2 * ∫ σ, B σ)) 0 0 := by
      refine hd.congr_of_eventuallyEq (Eventually.of_forall fun ε => ?_)
      show T / 2 * (ε * (∫ σ, A σ) + ε ^ 2 * ∫ σ, B σ) = T / 2 * _
      rw [← hint ε]
    have hd2 : HasDerivAt (fun ε : ℝ => T / 2 * (ε * (∫ σ, A σ) + ε ^ 2 * ∫ σ, B σ))
        (T / 2 * ∫ σ, A σ) 0 := by
      have := (((hasDerivAt_id (0:ℝ)).mul_const (∫ σ, A σ)).add
        ((hasDerivAt_pow 2 (0:ℝ)).mul_const (∫ σ, B σ))).const_mul (T / 2)
      refine (this.congr_deriv (by simp)).congr_of_eventuallyEq
        (Eventually.of_forall fun ε => by simp)
    have hIA : ∫ σ, A σ = 0 := by
      have h := hd2.unique hd'
      rcases mul_eq_zero.1 h with h | h
      · exact absurd (by linarith : T = 0) hT
      · exact h
    have hibp : ∀ a : Fin 2, ∫ σ, partialDeriv X a μ0 σ * fderiv ℝ φ σ (Pi.single a 1)
        = - ∫ σ, secondPartialDeriv X a a μ0 σ * φ σ := by
      intro a
      rw [integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
        (f := fun σ => partialDeriv X a μ0 σ) (g := φ) (v := Pi.single a 1) ?_ (hPdφ a)
        (((hP a).continuous.mul hφ.continuous).integrable_of_hasCompactSupport hφc.mul_left)
        (fun x _ => ((hP a).differentiable (by norm_num)) x) (fun x _ => hφd x)]
      · simp_rw [hbridge]
      · simp_rw [hbridge]
        exact hSφ a
    have hIA' : ∫ σ, A σ = η * (2 * ((∫ σ, partialDeriv X 0 μ0 σ * fderiv ℝ φ σ (Pi.single 0 1))
        - ∫ σ, partialDeriv X 1 μ0 σ * fderiv ℝ φ σ (Pi.single 1 1))) := by
      rw [hA, integral_const_mul, integral_const_mul, integral_sub (hPdφ 0) (hPdφ 1)]
    have hW' : ∫ σ, φ σ • W σ = (∫ σ, secondPartialDeriv X 0 0 μ0 σ * φ σ)
        - ∫ σ, secondPartialDeriv X 1 1 μ0 σ * φ σ := by
      rw [← integral_sub (hSφ 0) (hSφ 1)]
      congr 1
      funext σ
      simp only [hW, smul_eq_mul]
      ring
    rw [hW']
    rw [hIA', hibp, hibp] at hIA
    rcases mul_eq_zero.1 hIA with h | h
    · exact absurd h hη0
    · linarith
  have hae := ae_eq_zero_of_integral_contDiff_smul_eq_zero (μ := volume) hWc.locallyIntegrable key
  have hWz : W = 0 := (hWc.ae_eq_iff_eq volume continuous_zero).1 hae
  exact congrFun hWz σ0
