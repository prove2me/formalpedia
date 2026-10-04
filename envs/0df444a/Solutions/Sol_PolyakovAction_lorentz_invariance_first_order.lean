-- Prove2me | solution 1 for PolyakovAction.lorentz_invariance_first_order
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T08:03:39.234498+00:00
-- url     : https://prove2.me/submissions/edb4cd3e-5379-4d97-83ad-25bd49c9f832

import Mathlib
import Definitions.Def_PolyakovAction_Defs

open MeasureTheory Filter Asymptotics
open scoped Matrix Topology

namespace PolyakovAction

lemma bform_e48f28f8 {D : ℕ} (g : Matrix (Fin D) (Fin D) ℝ) (x y : Fin D → ℝ) :
    (∑ μ, ∑ ν, g μ ν * x μ * y ν) = x ⬝ᵥ (g *ᵥ y) := by
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ => ?_
  ring

lemma antisym_e48f28f8 {D : ℕ} (g ω : Matrix (Fin D) (Fin D) ℝ)
    (hg : gᵀ = g) (hω : (g * ω)ᵀ = -(g * ω)) (x y : Fin D → ℝ) :
    x ⬝ᵥ (g *ᵥ (ω *ᵥ y)) + (ω *ᵥ x) ⬝ᵥ (g *ᵥ y) = 0 := by
  have h1 : (ω *ᵥ x) ⬝ᵥ (g *ᵥ y) = x ⬝ᵥ ((ωᵀ * g) *ᵥ y) := by
    rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec x ωᵀ, Matrix.vecMul_transpose]
  have h2 : ωᵀ * g = -(g * ω) := by
    rw [← hω, Matrix.transpose_mul, hg]
  rw [h1, h2, Matrix.mulVec_mulVec, Matrix.neg_mulVec, dotProduct_neg, add_neg_cancel]

lemma hasFDerivY_e48f28f8 {D : ℕ} (ω : Matrix (Fin D) (Fin D) ℝ) (X : Worldsheet → Spacetime D)
    (hX : Differentiable ℝ X) (σ : Worldsheet) :
    HasFDerivAt (fun σ => ω *ᵥ X σ)
      ((LinearMap.toContinuousLinearMap (Matrix.mulVecLin ω)).comp (fderiv ℝ X σ)) σ := by
  have := (LinearMap.toContinuousLinearMap (Matrix.mulVecLin ω)).hasFDerivAt.comp σ
    (hX σ).hasFDerivAt
  exact this

lemma pdY_e48f28f8 {D : ℕ} (ω : Matrix (Fin D) (Fin D) ℝ) (X : Worldsheet → Spacetime D)
    (hX : Differentiable ℝ X) (a : Fin 2) (μ : Fin D) (σ : Worldsheet) :
    partialDeriv (fun σ => ω *ᵥ X σ) a μ σ
      = (ω *ᵥ (fderiv ℝ X σ (Pi.single a 1))) μ := by
  unfold partialDeriv
  rw [(hasFDerivY_e48f28f8 ω X hX σ).fderiv]
  simp

lemma pdXY_e48f28f8 {D : ℕ} (ω : Matrix (Fin D) (Fin D) ℝ) (X : Worldsheet → Spacetime D)
    (hX : Differentiable ℝ X) (ε : ℝ) (a : Fin 2) (μ : Fin D) (σ : Worldsheet) :
    partialDeriv (fun σ => X σ + ε • (ω *ᵥ X σ)) a μ σ
      = fderiv ℝ X σ (Pi.single a 1) μ + ε * (ω *ᵥ (fderiv ℝ X σ (Pi.single a 1))) μ := by
  unfold partialDeriv
  have hd : HasFDerivAt (fun σ => X σ + ε • (ω *ᵥ X σ)) _ σ :=
    (hX σ).hasFDerivAt.add ((hasFDerivY_e48f28f8 ω X hX σ).const_smul ε)
  rw [hd.fderiv]
  simp

lemma induced_e48f28f8 {D : ℕ} (g ω : Matrix (Fin D) (Fin D) ℝ)
    (hg : gᵀ = g) (hω : (g * ω)ᵀ = -(g * ω)) (X : Worldsheet → Spacetime D)
    (hX : Differentiable ℝ X) (ε : ℝ) (σ : Worldsheet) (a b : Fin 2) :
    inducedMetric (fun _ => g) (fun σ => X σ + ε • (ω *ᵥ X σ)) σ a b
      = inducedMetric (fun _ => g) X σ a b
        + ε ^ 2 * inducedMetric (fun _ => g) (fun σ => ω *ᵥ X σ) σ a b := by
  unfold inducedMetric
  simp only [Matrix.of_apply]
  simp only [pdXY_e48f28f8 ω X hX, pdY_e48f28f8 ω X hX]
  simp only [partialDeriv]
  set u := fderiv ℝ X σ (Pi.single a 1)
  set v := fderiv ℝ X σ (Pi.single b 1)
  have key := antisym_e48f28f8 g ω hg hω u v
  have e1 : (∑ μ, ∑ ν, g μ ν * (u μ + ε * (ω *ᵥ u) μ) * (v ν + ε * (ω *ᵥ v) ν))
      = (∑ μ, ∑ ν, g μ ν * u μ * v ν)
        + ε * ((∑ μ, ∑ ν, g μ ν * u μ * (ω *ᵥ v) ν) + ∑ μ, ∑ ν, g μ ν * (ω *ᵥ u) μ * v ν)
        + ε ^ 2 * ∑ μ, ∑ ν, g μ ν * (ω *ᵥ u) μ * (ω *ᵥ v) ν := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ => ?_
    ring
  have e2 : (∑ μ, ∑ ν, g μ ν * u μ * (ω *ᵥ v) ν) + ∑ μ, ∑ ν, g μ ν * (ω *ᵥ u) μ * v ν = 0 := by
    rw [bform_e48f28f8, bform_e48f28f8]
    exact key
  rw [e1, e2, mul_zero, add_zero]

lemma lagr_e48f28f8 {D : ℕ} (g ω : Matrix (Fin D) (Fin D) ℝ)
    (hg : gᵀ = g) (hω : (g * ω)ᵀ = -(g * ω)) (h : Worldsheet → Matrix (Fin 2) (Fin 2) ℝ)
    (X : Worldsheet → Spacetime D) (hX : Differentiable ℝ X) (ε : ℝ) (σ : Worldsheet) :
    polyakovLagrangian (fun _ => g) h (fun σ => X σ + ε • (ω *ᵥ X σ)) σ
      = polyakovLagrangian (fun _ => g) h X σ
        + ε ^ 2 * polyakovLagrangian (fun _ => g) h (fun σ => ω *ᵥ X σ) σ := by
  unfold polyakovLagrangian
  simp only [induced_e48f28f8 g ω hg hω X hX ε σ, mul_add, Finset.sum_add_distrib,
    Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

end PolyakovAction

open PolyakovAction MeasureTheory Filter Asymptotics in open scoped Matrix Topology in
theorem solution {D : ℕ} (T : ℝ) (g : Matrix (Fin D) (Fin D) ℝ)
    (hg : gᵀ = g) (ω : Matrix (Fin D) (Fin D) ℝ) (hω : (g * ω)ᵀ = -(g * ω))
    (h : Worldsheet → Matrix (Fin 2) (Fin 2) ℝ) (X : Worldsheet → Spacetime D)
    (hX : Differentiable ℝ X) (U : Set Worldsheet)
    (hL : IntegrableOn (polyakovLagrangian (fun _ => g) h X) U)
    (hLω : IntegrableOn (polyakovLagrangian (fun _ => g) h (fun σ => ω *ᵥ X σ)) U) :
    (fun ε : ℝ => polyakovAction T (fun _ => g) h (fun σ => X σ + ε • (ω *ᵥ X σ)) U
        - polyakovAction T (fun _ => g) h X U) =O[𝓝 0] (fun ε : ℝ => ε ^ 2) := by
  have hfun : (fun ε : ℝ => polyakovAction T (fun _ => g) h (fun σ => X σ + ε • (ω *ᵥ X σ)) U
        - polyakovAction T (fun _ => g) h X U)
      = fun ε : ℝ => (T / 2 * ∫ σ in U, polyakovLagrangian (fun _ => g) h
          (fun σ => ω *ᵥ X σ) σ) * ε ^ 2 := by
    funext ε
    unfold polyakovAction
    simp_rw [lagr_e48f28f8 g ω hg hω h X hX ε]
    rw [integral_add hL (hLω.const_mul (ε ^ 2)), integral_const_mul]
    ring
  rw [hfun]
  exact (isBigO_refl (fun ε : ℝ => ε ^ 2) (𝓝 0)).const_mul_left _
