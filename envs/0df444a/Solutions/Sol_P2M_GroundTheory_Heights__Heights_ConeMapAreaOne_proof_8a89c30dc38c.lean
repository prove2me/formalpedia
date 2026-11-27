-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ConeMapAreaOne_proof_8a89c30dc38c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:53:35.318548+00:00
-- url     : https://prove2.me/submissions/de6486cf-1f1a-4404-abaf-d05736a908a8

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeMapAreaOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsAreaFormulaInj
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeIntegralMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFrameJacobianSum
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_VolumePreservingUncurry
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeMapAreaOne
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ConeMapAreaFormula_splitE_apply_152b7a9725df
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ConeMapAreaFormula_measurePreserving_splitE_5c13f987f480
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ConeMapAreaFormula_hasFDerivAt_coneMapE_b63df86745a8
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ConeMapAreaFormula_areaJacobian_coneMapE_d9a776937d95
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ConeMapAreaFormula_lintegral_cone_prod_6b346da01c58
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ConeMapAreaFormula_aemeasurable_coneIntegrand_23ef9853180b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ConeMapAreaFormula_hausdorff_eq_zero_of_lt_3901e9dd64fb
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ConeMapAreaFormula_volume_ball_E_03894f69c9b1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ConeMapAreaFormula_coordBall_eq_9fbc0a1de5fa
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_isometry_zeroExt_b287ac62694e
import Theorems.Thm_ReciprocityTheory_AnForm_Osgood_osgood


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MeasureTheory Module
open scoped ENNReal NNReal ComplexOrder
open ConeMapAreaFormula
namespace GroundTheory.Heights₂.Heights
namespace ConeMapAreaOne
theorem _root_.solution (hA : AreaFormulaInj.Statement) : ConeMapAreaOne.Statement := by
  intro n e U D v F hU hD hDU hv hinj hF
  by_cases hn : e + 1 ≤ n
  swap
  · rw [hausdorff_eq_zero_of_lt (by omega : n < e + 1)]
    simp
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  have hfin : finrank ℝ (EuclideanSpace ℂ (Fin (e + 1))) = 2 * (e + 1) := by
    rw [finrank_real_of_complex, finrank_euclideanSpace_fin]
  set S := {q : (Fin e → ℂ) × ℂ | q.1 ∈ D ∧ q.2 ≠ 0} with hSdef
  have hSm : MeasurableSet S := hD.prod (measurableSet_singleton (0 : ℂ)).compl
  set AE := splitE e ⁻¹' S with hAEdef
  have hAEm : MeasurableSet AE := (splitE e).measurable hSm
  set UE := {p : EuclideanSpace ℂ (Fin (e + 1)) | tailL e p ∈ U} with hUEdef
  have hUE : IsOpen UE := hU.preimage (tailL e).continuous
  have hAU : AE ⊆ UE := by
    intro p hp
    have h1 := hp.1
    rw [splitE_apply] at h1
    exact hDU h1
  have hdiff : ∀ p ∈ UE, DifferentiableAt ℂ v (tailL e p) := fun p hp =>
    hv.differentiableAt (hU.mem_nhds hp)

  have hvC : ContDiffOn ℂ 1 v U := by
    refine contDiffOn_pi.2 fun i => ?_
    have hvi : DifferentiableOn ℂ (fun x => v x i) U := fun x hx =>
      ((differentiableAt_pi.1 (hv.differentiableAt (hU.mem_nhds hx))) i).differentiableWithinAt
    exact (ReciprocityTheory.AnForm.Osgood.osgood e U _ hU hvi).contDiffOn (n := 1) hU.uniqueDiffOn
  have hC : ContDiffOn ℝ 1 (coneMapE (n := e + 1 + k) v) UE := by
    have h1 : ContDiffOn ℂ 1 (fun p => WithLp.toLp 2 (v (tailL e p)) :
        EuclideanSpace ℂ (Fin (e + 1)) → EuclideanSpace ℂ (Fin (e + 1 + k))) UE :=
      (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin (e + 1 + k) => ℂ)).symm.contDiff.comp_contDiffOn
        (hvC.comp (tailL e).contDiff.contDiffOn (fun p hp => hp))
    exact ((EuclideanSpace.proj (0 : Fin (e + 1)) :
      EuclideanSpace ℂ (Fin (e + 1)) →L[ℂ] ℂ).contDiff.contDiffOn.smul h1).restrict_scalars ℝ
  have hcomp : coneMapE (n := e + 1 + k) v =
      (fun q : (Fin e → ℂ) × ℂ => q.2 • WithLp.toLp 2 (v q.1)) ∘ splitE e := by
    funext p
    rw [Function.comp_apply, splitE_apply]
    rfl
  have hinjE : Set.InjOn (coneMapE (n := e + 1 + k) v) AE := by
    rw [hcomp]
    exact hinj.comp (splitE e).injective.injOn (fun p hp => hp)
  have himg : coneMapE (n := e + 1 + k) v '' AE =
      (fun q : (Fin e → ℂ) × ℂ => q.2 • WithLp.toLp 2 (v q.1)) '' S := by
    rw [hcomp, Set.image_comp, Set.image_preimage_eq _ (splitE e).surjective]
  have key := hA (EuclideanSpace ℂ (Fin (e + 1))) (EuclideanSpace ℂ (Fin (e + 1 + k))) (2 * (e + 1))
    hfin UE AE (coneMapE v) F hUE hC hAU hAEm hinjE hF
  rw [himg] at key
  rw [key]
  have hJ : Set.EqOn (fun p => F (coneMapE v p) * ENNReal.ofReal (areaJacobian
      (fderiv ℝ (coneMapE (n := e + 1 + k) v) p : EuclideanSpace ℂ (Fin (e + 1)) →ₗ[ℝ]
        EuclideanSpace ℂ (Fin (e + 1 + k))))) (fun p => coneIntegrand v F (splitE e p)) AE := by
    intro p hp
    have hd := hdiff p (hAU hp)
    simp only
    rw [(hasFDerivAt_coneMapE hd).differentiableAt.fderiv_restrictScalars ℝ]
    rw [show ((ContinuousLinearMap.restrictScalars ℝ (fderiv ℂ (coneMapE (n := e + 1 + k) v) p) :
        EuclideanSpace ℂ (Fin (e + 1)) →L[ℝ] EuclideanSpace ℂ (Fin (e + 1 + k))) :
          EuclideanSpace ℂ (Fin (e + 1)) →ₗ[ℝ] EuclideanSpace ℂ (Fin (e + 1 + k))) =
        ((fderiv ℂ (coneMapE (n := e + 1 + k) v) p : EuclideanSpace ℂ (Fin (e + 1)) →ₗ[ℂ]
          EuclideanSpace ℂ (Fin (e + 1 + k))).restrictScalars ℝ) from rfl]
    rw [areaJacobian_coneMapE hd, coneIntegrand, splitE_apply]
    rfl
  rw [setLIntegral_congr_fun hAEm hJ]
  have hexp : ((2 * (e + 1) : ℕ) : ℝ) = (finrank ℝ (EuclideanSpace ℂ (Fin (e + 1))) : ℝ) := by
    rw [hfin]
  rw [coordBall_eq (e + 1) k, hexp, (isometry_zeroExt (e + 1) k).hausdorffMeasure_image
    (Or.inl (by positivity))]
  have hμ := Measure.isAddLeftInvariant_eq_smul
    (μH[(finrank ℝ (EuclideanSpace ℂ (Fin (e + 1))) : ℝ)] : Measure (EuclideanSpace ℂ (Fin (e + 1))))
    volume
  rw [hμ, Measure.restrict_smul, lintegral_smul_measure, Measure.smul_apply,
    (measurePreserving_splitE e).setLIntegral_comp_preimage_emb (splitE e).measurableEmbedding,
    lintegral_cone_prod _ (aemeasurable_coneIntegrand hD hDU hv hF), volume_ball_E]
  simp only [ENNReal.smul_def, smul_eq_mul, coneIntegrand]
  ring
end ConeMapAreaOne
end GroundTheory.Heights₂.Heights
