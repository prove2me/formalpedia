-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ProjectionFormula_proof_7125d6e08770
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:40:55.17661+00:00
-- url     : https://prove2.me/submissions/587b2a1c-0d12-4373-823a-33c1b51eb21c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsArea
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StAreaMultiplicity
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFrameJacobianSum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGraphAreaHolomorphic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PProjectionFormula
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_graphPt_injective_c1602eb4686f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_differentiableAt_graphPt_1c88044ce855
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_continuous_areaJacobian_b8921d31322f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_frameProjLin_apply_c62a8e9c3850


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
open MeasureTheory Module
open scoped ENNReal
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace ProjectionFormula
theorem _root_.solution (h1 : AreaMultiplicity.Statement) (h2 : FrameJacobianSum.Statement)
    (h3 : GraphAreaHolomorphic.Statement) : ProjectionFormula.Statement := by
  classical
  intro d m n e Ω F hΩ hF b B hB
  have hGd : ∀ x ∈ Ω, DifferentiableAt ℂ (graphPt e F) x := fun x hx =>
    differentiableAt_graphPt e (hF.differentiableAt (hΩ.mem_nhds hx))
  set A := Ω ∩ graphPt e F ⁻¹' B with hAdef
  have hAΩ : A ⊆ Ω := Set.inter_subset_left
  have hA : MeasurableSet A := by
    have hc : ContinuousOn (graphPt e F) Ω := fun x hx => (hGd x hx).continuousAt.continuousWithinAt
    have hm := (hc.measurable_piecewise (continuousOn_const (c := (0 : EuclideanSpace ℂ (Fin n))))
      hΩ.measurableSet) hB
    have hEq : A = Ω ∩ (Ω.piecewise (graphPt e F) fun _ => 0) ⁻¹' B := by
      ext x
      simp only [hAdef, Set.mem_inter_iff, Set.mem_preimage]
      constructor
      · rintro ⟨hx, hx'⟩
        exact ⟨hx, by rw [Set.piecewise_eq_of_mem _ _ _ hx]; exact hx'⟩
      · rintro ⟨hx, hx'⟩
        exact ⟨hx, by rw [Set.piecewise_eq_of_mem _ _ _ hx] at hx'; exact hx'⟩
    rw [hEq]
    exact hΩ.measurableSet.inter hm

  let πR : ∀ I : Finset (Fin n), EuclideanSpace ℂ (Fin n) →L[ℝ] EuclideanSpace ℂ I := fun I =>
    (LinearMap.toContinuousLinearMap (frameProjLin b I)).restrictScalars ℝ
  have hpt : ∀ x ∈ A, ENNReal.ofReal (areaJacobian
      (fderiv ℝ (graphPt e F) x : EuclideanSpace ℂ (Fin d) →ₗ[ℝ] EuclideanSpace ℂ (Fin n))) =
      ∑ I ∈ Finset.univ.powersetCard d, ENNReal.ofReal (areaJacobian
        ((πR I).comp (fderiv ℝ (graphPt e F) x) : EuclideanSpace ℂ (Fin d) →ₗ[ℝ] EuclideanSpace ℂ I)) := by
    intro x hx
    set L := fderiv ℂ (graphPt e F) x with hL
    have e0 : ((L.restrictScalars ℝ : EuclideanSpace ℂ (Fin d) →L[ℝ] EuclideanSpace ℂ (Fin n)) :
        EuclideanSpace ℂ (Fin d) →ₗ[ℝ] EuclideanSpace ℂ (Fin n)) =
        (L : EuclideanSpace ℂ (Fin d) →ₗ[ℂ] EuclideanSpace ℂ (Fin n)).restrictScalars ℝ :=
      LinearMap.ext fun v => rfl
    have eI : ∀ I : Finset (Fin n), (((πR I).comp (L.restrictScalars ℝ)) :
        EuclideanSpace ℂ (Fin d) →ₗ[ℝ] EuclideanSpace ℂ I) =
        (frameProjLin b I ∘ₗ (L : EuclideanSpace ℂ (Fin d) →ₗ[ℂ] EuclideanSpace ℂ (Fin n))).restrictScalars ℝ :=
      fun I => LinearMap.ext fun v => rfl
    rw [(hGd x (hAΩ hx)).fderiv_restrictScalars ℝ, ← hL, e0, ← ENNReal.ofReal_sum_of_nonneg]
    · simp only [eI]
      exact congrArg ENNReal.ofReal (h2 d n _ b)
    · exact fun I _ => Real.sqrt_nonneg _
  have hmeas : ∀ I : Finset (Fin n), AEMeasurable (fun x => ENNReal.ofReal (areaJacobian
      ((πR I).comp (fderiv ℝ (graphPt e F) x) : EuclideanSpace ℂ (Fin d) →ₗ[ℝ] EuclideanSpace ℂ I)))
      ((μH[((2 * d : ℕ) : ℝ)]).restrict A) := fun I =>
    ((ENNReal.continuous_ofReal.comp (continuous_areaJacobian.comp
      (continuous_const.clm_comp continuous_id))).measurable.comp
        (measurable_fderiv ℝ (graphPt e F))).aemeasurable
  rw [(Set.image_inter_preimage (graphPt e F) Ω B).symm, h3 d m n e Ω F hΩ hF A hAΩ hA,
    setLIntegral_congr_fun hA hpt, lintegral_finsetSum' _ fun I _ => hmeas I]
  refine Finset.sum_congr rfl fun I hI => ?_
  have hcard : I.card = d := (Finset.mem_powersetCard.1 hI).2
  have hfr1 : finrank ℝ (EuclideanSpace ℂ (Fin d)) = 2 * d := by
    rw [finrank_real_of_complex, finrank_euclideanSpace, Fintype.card_fin]
  have hfr2 : finrank ℝ (EuclideanSpace ℂ I) = 2 * d := by
    rw [finrank_real_of_complex, finrank_euclideanSpace, Fintype.card_coe, hcard]
  have hder : ∀ x ∈ A, HasFDerivWithinAt (fun x => frameProjLin b I (graphPt e F x))
      ((πR I).comp (fderiv ℝ (graphPt e F) x)) A x := fun x hx =>
    ((πR I).hasFDerivAt.comp x ((hGd x (hAΩ hx)).restrictScalars ℝ).hasFDerivAt).hasFDerivWithinAt
  rw [h1 _ _ (2 * d) hfr1 hfr2 A _ _ hA hder]
  refine lintegral_congr fun y => ?_
  have hset : {z ∈ graphPt e F '' A | frameProj b I z = WithLp.ofLp y} =
      graphPt e F '' {x ∈ A | frameProjLin b I (graphPt e F x) = y} := by
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_image]
    constructor
    · rintro ⟨⟨x, hx, rfl⟩, hz⟩
      exact ⟨x, ⟨hx, WithLp.ofLp_injective 2 (by rw [frameProjLin_apply]; exact hz)⟩, rfl⟩
    · rintro ⟨x, ⟨hx, hxy⟩, rfl⟩
      exact ⟨⟨x, hx, rfl⟩, by rw [← frameProjLin_apply, hxy]⟩
  unfold frameFibreCount
  rw [hset, (graphPt_injective e F).injOn.encard_image]
end ProjectionFormula
end GroundTheory.Heights₂.Heights
