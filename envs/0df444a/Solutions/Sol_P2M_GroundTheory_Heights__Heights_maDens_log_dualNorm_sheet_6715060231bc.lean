-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_maDens_log_dualNorm_sheet_6715060231bc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:52:59.354369+00:00
-- url     : https://prove2.me/submissions/873a6769-ab4d-4947-88d6-ff274c83142e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StConePolar
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StConeChartGram
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLinearNoetherNormalization
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PChartGramMA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeLogBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PConePolar
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_anForm_maDens_eq_geo_maDensity_553a74f4fa53
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartGramMA_proof_e3fb81211f72
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ConeLogBound_proof_ab4a666aa1df
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HermNorm_dualNorm_pos_3da77c812dcb


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory Matrix ComplexSets Filter Topology
noncomputable section
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {n e : ℕ} (h : HermNorm n) (J : Ideal (MvPolynomial (Fin n) ℂ))
    (ℓ : Fin n → ℂ) (A : Matrix (Fin e) (Fin n) ℂ) (y : Fin e → ℂ) (x : Fin n → ℂ)
    (s : (Fin e → ℂ) → Fin n → ℂ) (hx : x ∈ fibre (J ⊔ Ideal.span {linForm ℓ - 1}) A y)
    (hs : IsSheetAt (J ⊔ Ideal.span {linForm ℓ - 1}) A x s) :
    ReciprocityTheory.AnForm.maDens (fun k => (fun (_ : Fin e) x => Real.log (h.dualNorm x)) k ∘ s) y =
      (e.factorial : ℝ) / Real.pi ^ e * gramVol (fun y' => (h.matᵀ)⁻¹ *ᵥ s y') y /
        h.dualNorm x ^ (2 * (e + 1)) := by
  obtain ⟨U, hU, hyU, hdiff, hsx, -, -⟩ := hs
  obtain ⟨hxZ, rfl⟩ := hx
  have hx0 : x ≠ 0 := by
    rintro rfl
    have h1 : eval (0 : Fin n → ℂ) (linForm ℓ - 1) = 0 :=
      hxZ _ (Ideal.mem_sup_right (Ideal.subset_span rfl))
    rw [map_sub, map_one, linForm, map_sum] at h1
    simp at h1
  have hdual : ∀ z, h.dualNorm z = ‖WithLp.toLp 2 ((h.matᵀ)⁻¹ *ᵥ z)‖ := fun z => by
    simp [HermNorm.dualNorm, EuclideanSpace.norm_eq]
  have hv : ∀ᶠ y' in 𝓝 (A *ᵥ x), DifferentiableAt ℂ (fun y' => (h.matᵀ)⁻¹ *ᵥ s y') y' := by
    filter_upwards [hU.mem_nhds hyU] with y' hy'
    have hs' := (hdiff y' hy').differentiableAt (hU.mem_nhds hy')
    exact (LinearMap.toContinuousLinearMap (Matrix.mulVecLin (h.matᵀ)⁻¹)).differentiableAt.comp y' hs'
  have hne : (fun y' => (h.matᵀ)⁻¹ *ᵥ s y') (A *ᵥ x) ≠ 0 := by
    intro h0
    have hpos := HermNorm.dualNorm_pos h hx0
    rw [hdual, ← hsx, show (h.matᵀ)⁻¹ *ᵥ s (A *ᵥ x) = 0 from h0] at hpos
    simp at hpos
  have key := ChartGramMA.proof e n _ _ hv hne
  have hF : (fun k : Fin e => (fun (_ : Fin e) x => Real.log (h.dualNorm x)) k ∘ s) =
      fun _ y' => Real.log ‖WithLp.toLp 2 ((h.matᵀ)⁻¹ *ᵥ s y')‖ := by
    funext k y'
    simp only [Function.comp_apply, hdual]
  rw [hF, anForm_maDens_eq_geo_maDensity, key, hsx, ← hdual]
end GroundTheory.Heights₂.Heights
