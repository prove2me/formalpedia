-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LatticeLemmas_gramDet_eq_of_norm_eq_284c59650304
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:53:24.708367+00:00
-- url     : https://prove2.me/submissions/51a2e45d-5cbf-48ad-a286-a62fca1d393e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PDiagonalChange
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeLemmas_span_fibreVec_eq_top_3f80ac305458

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LatticeLemmas
open NumberField NumberField.ComplexEmbedding TensorProduct ComplexAt Matrix
open GroundTheory.Heights₂.Heights
noncomputable section
variable {K : Type*} [Field K] [NumberField K] {E : Type*} [AddCommGroup E] [Module (𝓞 K) E]
  [Module.Finite (𝓞 K) E] [Module.Projective (𝓞 K) E]
namespace GroundTheory.Heights₂.Heights.LatticeLemmas
theorem _root_.solution (h h' : HermitianMetric K E) (σ : K →+* ℂ)
    (T : Fibre σ E →ₗ[ℂ] Fibre σ E)
    (hT : ∀ x, ‖FibreSpace.equiv h' σ x‖ = ‖FibreSpace.equiv h σ (T x)‖) {ι : Type*} [Fintype ι]
    [DecidableEq ι] {s : ι → E} (hs : LinearIndependent (𝓞 K) s)
    (hcard : Fintype.card ι = Module.finrank (𝓞 K) E) :
    gramDet h' σ s = ‖LinearMap.det T‖ ^ 2 * gramDet h σ s := by
  have kadd : ∀ (c : ℂ) (x y : Fibre σ E), ‖FibreSpace.equiv h' σ x + c • FibreSpace.equiv h' σ y‖ =
      ‖FibreSpace.equiv h σ (T x) + c • FibreSpace.equiv h σ (T y)‖ := by
    intro c x y
    rw [← map_smul, ← map_add, hT, map_add, map_add, map_smul, map_smul]
  have ksub : ∀ (c : ℂ) (x y : Fibre σ E), ‖FibreSpace.equiv h' σ x - c • FibreSpace.equiv h' σ y‖ =
      ‖FibreSpace.equiv h σ (T x) - c • FibreSpace.equiv h σ (T y)‖ := by
    intro c x y
    rw [← map_smul, ← map_sub, hT, map_sub, map_sub, map_smul, map_smul]
  have hinner : ∀ x y : Fibre σ E, inner ℂ (FibreSpace.equiv h' σ x) (FibreSpace.equiv h' σ y) =
      inner ℂ (FibreSpace.equiv h σ (T x)) (FibreSpace.equiv h σ (T y)) := by
    intro x y
    have e1 := kadd 1 x y
    have e2 := ksub 1 x y
    simp only [one_smul] at e1 e2
    rw [inner_eq_sum_norm_sq_div_four (𝕜 := ℂ) (FibreSpace.equiv h' σ x),
      inner_eq_sum_norm_sq_div_four (𝕜 := ℂ) (FibreSpace.equiv h σ (T x)), e1, e2, kadd, ksub]
  let bv : Module.Basis ι ℂ (FibreSpace h σ) :=
    Module.Basis.mk (linearIndependent_fibreVec h σ hs) (span_fibreVec_eq_top h σ hs hcard).ge
  let S : FibreSpace h σ →ₗ[ℂ] FibreSpace h σ := (FibreSpace.equiv h σ).conj T
  let B := LinearMap.toMatrix bv bv S
  have hS : ∀ e : E, S (fibreVec h σ e) = FibreSpace.equiv h σ (T ((1 : ComplexAt σ) ⊗ₜ e)) := by
    intro e
    simp only [S, LinearEquiv.conj_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, fibreVec,
      LinearEquiv.symm_apply_apply]
  have hgram : (gram ℂ fun i ↦ fibreVec h' σ (s i)) = gram ℂ fun j ↦ ∑ i, B i j • bv i := by
    ext i j
    simp only [gram_apply]
    have hj : ∀ j, ∑ i, B i j • bv i = S (fibreVec h σ (s j)) := by
      intro j
      have := bv.sum_repr (S (bv j))
      simp only [B, LinearMap.toMatrix_apply]
      rw [this, Module.Basis.mk_apply]
    rw [hj, hj, hS, hS]
    exact hinner _ _
  have hbv : (⇑bv : ι → FibreSpace h σ) = fun i ↦ fibreVec h σ (s i) := funext fun i ↦ Module.Basis.mk_apply _ _ _
  have hdet : B.det = LinearMap.det T := by
    rw [LinearMap.det_toMatrix]
    exact LinearMap.det_conj T (FibreSpace.equiv h σ)
  simp only [gramDet]
  rw [hgram, gram_comb, hbv, det_mul, det_mul, det_conjTranspose, mul_comm _ B.det, ← mul_assoc,
    RCLike.star_def, Complex.mul_conj, Complex.re_ofReal_mul, Complex.normSq_eq_norm_sq, hdet]
end GroundTheory.Heights₂.Heights.LatticeLemmas
