-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ConeSheetGramLintegral_proof_0bff92a5f457
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:54:27.685894+00:00
-- url     : https://prove2.me/submissions/ffdeb29d-a733-4a4f-87aa-10b62affd169

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StConeSliceSheetParam
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeMapArea
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeSheetAreaLintegral
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PConeSheetGramLintegral
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IsSheetAt_eventuallyEq_5bf3495b137a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_aemeasurable_coneTerm_4ac5814534a0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_gramVol_congr_72a101c5afe4


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
open MvPolynomial MeasureTheory Matrix Filter Topology Set ComplexSets
open scoped ENNReal
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace ConeSheetGramLintegral
theorem _root_.solution (hPar : ConeSliceSheetParam.Statement)
    (hArea : ConeMapArea.Statement) : ConeSheetGramLintegral.Statement := by
  classical
  intro n e h J ℓ A F hJ hdim hℓ hA hF
  obtain ⟨U, D, N, s, hUD, hdisj, hnull, hfib, hinj, hsub, hcov⟩ := hPar n e h J ℓ A hJ hdim hℓ hA

  set v : (Σ k, Fin (N k)) → (Fin e → ℂ) → (Fin n → ℂ) :=
    fun i y => (h.matᵀ)⁻¹ *ᵥ s i.1 i.2 y with hv_def
  have hvd : ∀ i : Σ k, Fin (N k), DifferentiableOn ℂ (v i) (U i.1) := fun i =>
    (Matrix.mulVecLin (h.matᵀ)⁻¹).toContinuousLinearMap.differentiable.comp_differentiableOn
      ((hUD i.1).2.2.2 i.2)

  set H : (Σ k, Fin (N k)) → (Fin e → ℂ) → ℝ≥0∞ := fun i y =>
    ∫⁻ t : ℂ, F (t • WithLp.toLp 2 (v i y)) * ENNReal.ofReal (‖t‖ ^ (2 * e) * gramVol (v i) y)
    with hH_def
  have hHm : ∀ i : Σ k, Fin (N k), AEMeasurable (H i) (volume.restrict (D i.1)) := fun i =>
    aemeasurable_coneTerm (hUD i.1).1 (hUD i.1).2.2.1 (hvd i) hF

  set G : (Fin e → ℂ) → ℝ≥0∞ := fun y =>
    ∑ᶠ x ∈ ComplexSets.fibre (J ⊔ Ideal.span {linForm ℓ - 1}) A y, ∫⁻ t : ℂ,
      F (t • WithLp.toLp 2 ((h.matᵀ)⁻¹ *ᵥ sheetThrough (J ⊔ Ideal.span {linForm ℓ - 1}) A x y)) *
        ENNReal.ofReal (‖t‖ ^ (2 * e) * gramVol (fun y' =>
          (h.matᵀ)⁻¹ *ᵥ sheetThrough (J ⊔ Ideal.span {linForm ℓ - 1}) A x y') y) with hG_def

  have hGD : ∀ k, ∀ y ∈ D k, G y = ∑ j : Fin (N k), H ⟨k, j⟩ y := by
    intro k y hy
    obtain ⟨hfe, hinjy, hsh⟩ := hfib k y ((hUD k).2.2.1 hy)
    simp only [hG_def, hfe]
    rw [finsum_mem_range hinjy, finsum_eq_sum_of_fintype]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hAy : A *ᵥ s k j y = y := by
      have hmem : s k j y ∈ ComplexSets.fibre (J ⊔ Ideal.span {linForm ℓ - 1}) A y := hfe ▸ ⟨j, rfl⟩
      exact hmem.2
    have hex : ∃ γ, IsSheetAt (J ⊔ Ideal.span {linForm ℓ - 1}) A (s k j y) γ := ⟨s k j, hsh j⟩
    have hch : sheetThrough (J ⊔ Ideal.span {linForm ℓ - 1}) A (s k j y) =ᶠ[𝓝 y] s k j := by
      have h1 : sheetThrough (J ⊔ Ideal.span {linForm ℓ - 1}) A (s k j y) = hex.choose := by
        simp only [sheetThrough, dif_pos hex]
      have h2 := hex.choose_spec.eventuallyEq (hsh j)
      rw [hAy] at h2
      rw [h1]
      exact h2
    have hval : sheetThrough (J ⊔ Ideal.span {linForm ℓ - 1}) A (s k j y) y = s k j y :=
      hch.eq_of_nhds
    have hgram : gramVol (fun y' =>
        (h.matᵀ)⁻¹ *ᵥ sheetThrough (J ⊔ Ideal.span {linForm ℓ - 1}) A (s k j y) y') y =
        gramVol (v ⟨k, j⟩) y :=
      gramVol_congr (hch.fun_comp fun f => (h.matᵀ)⁻¹ *ᵥ f)
    simp only [hH_def, hv_def, hval, hgram]

  set G' : (Fin e → ℂ) → ℝ≥0∞ := fun y =>
    ∑' k, (D k).indicator (fun y => ∑ j : Fin (N k), H ⟨k, j⟩ y) y with hG'_def
  have hGG' : G =ᵐ[volume] G' := by
    have hae : ∀ᵐ y ∂(volume : Measure (Fin e → ℂ)), y ∈ ⋃ k, D k := by
      rw [ae_iff]
      simpa [compl_def] using hnull
    filter_upwards [hae] with y hy
    obtain ⟨k, hk⟩ := mem_iUnion.1 hy
    simp only [hG'_def]
    rw [tsum_eq_single k, indicator_of_mem hk, hGD k y hk]
    intro k' hk'
    exact indicator_of_notMem (fun h' => (hdisj hk').le_bot ⟨h', hk⟩) _
  have hG'm : ∀ k, AEMeasurable ((D k).indicator fun y => ∑ j : Fin (N k), H ⟨k, j⟩ y) volume :=
    fun k => (aemeasurable_indicator_iff (hUD k).2.1).2
      (Finset.aemeasurable_fun_sum _ fun j _ => hHm ⟨k, j⟩)
  refine ⟨(AEMeasurable.tsum hG'm).congr hGG'.symm, ?_⟩

  have hRHS : ∫⁻ y, G y = ∑' i : Σ k, Fin (N k), ∫⁻ y in D i.1, H i y := by
    rw [lintegral_congr_ae hGG', lintegral_tsum hG'm, ENNReal.tsum_sigma']
    refine tsum_congr fun k => ?_
    rw [lintegral_indicator (hUD k).2.1, lintegral_finsetSum' _ fun j _ => hHm ⟨k, j⟩,
      tsum_fintype]

  have hLHS : ∫⁻ z in {z : EuclideanSpace ℂ (Fin n) | ∀ q ∈ J, eval (h.pointOf z) q = 0}, F z
        ∂(Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)) =
      ∫⁻ z in (fun q : (Σ k, Fin (N k)) × (Fin e → ℂ) × ℂ => q.2.2 • WithLp.toLp 2 (v q.1 q.2.1)) ''
          {q | q.2.1 ∈ D q.1.1 ∧ q.2.2 ≠ 0}, F z
        ∂(Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)) := by
    refine setLIntegral_congr (ae_eq_set.2 ⟨hcov, ?_⟩)
    rw [sdiff_eq_empty.2 hsub, measure_empty]
  have hMap := hArea n e (Σ k, Fin (N k)) (fun i => U i.1) (fun i => D i.1) v F
    (fun i => ⟨(hUD i.1).1, (hUD i.1).2.1, (hUD i.1).2.2.1, hvd i⟩) hinj hF
  rw [hLHS, hMap]
  exact congrArg _ hRHS.symm
end ConeSheetGramLintegral
end GroundTheory.Heights₂.Heights
