-- Prove2me | solution 1 for PolyakovAction.diffeomorphism_invariance
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T09:16:58.015659+00:00
-- url     : https://prove2.me/submissions/139a0d3e-c4f8-49f5-8def-572767c59db7

import Mathlib
import Definitions.Def_PolyakovAction_Defs

open MeasureTheory Filter Asymptotics
open scoped Matrix Topology

set_option autoImplicit false

lemma p2m_50a0258b_frob (M N : Matrix (Fin 2) (Fin 2) ℝ) :
    ∑ a, ∑ b, M a b * N a b = Matrix.trace (M * Nᵀ) := by
  simp [Matrix.trace, Matrix.mul_apply, Matrix.transpose_apply]

lemma p2m_50a0258b_key (J H G : Matrix (Fin 2) (Fin 2) ℝ) (hJ : J.det ≠ 0) :
    ∑ a, ∑ b, (Jᵀ * H * J)⁻¹ a b * (Jᵀ * G * J) a b = ∑ a, ∑ b, H⁻¹ a b * G a b := by
  rw [p2m_50a0258b_frob, p2m_50a0258b_frob]
  have hu : IsUnit J.det := isUnit_iff_ne_zero.mpr hJ
  have hut : IsUnit Jᵀ.det := by rw [Matrix.det_transpose]; exact hu
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.transpose_mul, Matrix.transpose_mul,
    Matrix.transpose_transpose]
  have e1 : J⁻¹ * (H⁻¹ * Jᵀ⁻¹) * (Jᵀ * (Gᵀ * J)) = J⁻¹ * ((H⁻¹ * Gᵀ) * J) := by
    simp only [Matrix.mul_assoc]
    rw [Matrix.nonsing_inv_mul_cancel_left _ _ hut]
  rw [e1, Matrix.trace_mul_comm, Matrix.mul_nonsing_inv_cancel_right _ _ hu]

lemma p2m_50a0258b_alg (J H G : Matrix (Fin 2) (Fin 2) ℝ) :
    Real.sqrt (-(Jᵀ * H * J).det) * ∑ a, ∑ b, (Jᵀ * H * J)⁻¹ a b * (Jᵀ * G * J) a b
      = |J.det| * (Real.sqrt (-H.det) * ∑ a, ∑ b, H⁻¹ a b * G a b) := by
  have hd : -(Jᵀ * H * J).det = J.det ^ 2 * (-H.det) := by
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]; ring
  rw [hd, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]
  by_cases hJ : J.det = 0
  · simp [hJ]
  · rw [p2m_50a0258b_key J H G hJ]; ring

open PolyakovAction in
lemma p2m_50a0258b_induced {D : ℕ} (g : Spacetime D → Matrix (Fin D) (Fin D) ℝ)
    (X : Worldsheet → Spacetime D) (y : Worldsheet) :
    inducedMetric g X y = (Matrix.of fun a μ => partialDeriv X a μ y) * g (X y)
      * (Matrix.of fun a μ => partialDeriv X a μ y)ᵀ := by
  ext a b
  simp only [inducedMetric, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  ring

open PolyakovAction in
lemma p2m_50a0258b_pd {D : ℕ} (X : Worldsheet → Spacetime D) (φ : Worldsheet → Worldsheet)
    (L : Worldsheet →L[ℝ] Worldsheet) (x : Worldsheet) (hφ : HasFDerivAt φ L x)
    (hX : DifferentiableAt ℝ X (φ x)) (a : Fin 2) (μ : Fin D) :
    partialDeriv (X ∘ φ) a μ x
      = ∑ c, LinearMap.toMatrix' L.toLinearMap c a * partialDeriv X c μ (φ x) := by
  unfold partialDeriv
  rw [fderiv_comp x hX hφ.differentiableAt, hφ.fderiv]
  set v := L (Pi.single a 1) with hv
  have hdec : v = v 0 • (Pi.single 0 1 : Worldsheet) + v 1 • (Pi.single 1 1 : Worldsheet) := by
    ext i; fin_cases i <;> simp
  rw [ContinuousLinearMap.comp_apply, ← hv, hdec, map_add, map_smul, map_smul]
  simp only [Fin.sum_univ_two, LinearMap.toMatrix'_apply, ContinuousLinearMap.coe_coe, ← hv,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul]

open PolyakovAction in
lemma p2m_50a0258b_induced_comp {D : ℕ} (g : Spacetime D → Matrix (Fin D) (Fin D) ℝ)
    (X : Worldsheet → Spacetime D) (φ : Worldsheet → Worldsheet)
    (L : Worldsheet →L[ℝ] Worldsheet) (x : Worldsheet) (hφ : HasFDerivAt φ L x)
    (hX : DifferentiableAt ℝ X (φ x)) :
    inducedMetric g (X ∘ φ) x = (LinearMap.toMatrix' L.toLinearMap)ᵀ * inducedMetric g X (φ x)
      * LinearMap.toMatrix' L.toLinearMap := by
  have hP : (Matrix.of fun a μ => partialDeriv (X ∘ φ) a μ x)
      = (LinearMap.toMatrix' L.toLinearMap)ᵀ * (Matrix.of fun a μ => partialDeriv X a μ (φ x)) := by
    ext a μ
    simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply]
    exact p2m_50a0258b_pd X φ L x hφ hX a μ
  rw [p2m_50a0258b_induced, p2m_50a0258b_induced, hP, Function.comp_apply, Matrix.transpose_mul,
    Matrix.transpose_transpose]
  simp only [Matrix.mul_assoc]

open MeasureTheory PolyakovAction Matrix in
theorem solution {D : ℕ} (T : ℝ)
    (g : Spacetime D → Matrix (Fin D) (Fin D) ℝ)
    (h : Worldsheet → Matrix (Fin 2) (Fin 2) ℝ) (X : Worldsheet → Spacetime D)
    (φ : Worldsheet → Worldsheet) (φ' : Worldsheet → (Worldsheet →L[ℝ] Worldsheet))
    (s : Set Worldsheet) (hs : IsOpen s) (hφ : ∀ x ∈ s, HasFDerivAt φ (φ' x) x)
    (hinj : Set.InjOn φ s) (hX : ∀ x ∈ s, DifferentiableAt ℝ X (φ x)) :
    polyakovAction T g
        (fun σ' => (LinearMap.toMatrix' (φ' σ').toLinearMap)ᵀ * h (φ σ')
          * LinearMap.toMatrix' (φ' σ').toLinearMap)
        (X ∘ φ) s
      = polyakovAction T g h X (φ '' s) := by
  unfold polyakovAction
  rw [integral_image_eq_integral_abs_det_fderiv_smul volume hs.measurableSet
    (fun x hx => (hφ x hx).hasFDerivWithinAt) hinj]
  congr 1
  refine setIntegral_congr_fun hs.measurableSet fun x hx => ?_
  have hdet : (φ' x).det = (LinearMap.toMatrix' (φ' x).toLinearMap).det :=
    (LinearMap.det_toMatrix' _).symm
  simp only [polyakovLagrangian, smul_eq_mul]
  rw [hdet, p2m_50a0258b_induced_comp g X φ (φ' x) x (hφ x hx) (hX x hx)]
  exact p2m_50a0258b_alg _ _ _
