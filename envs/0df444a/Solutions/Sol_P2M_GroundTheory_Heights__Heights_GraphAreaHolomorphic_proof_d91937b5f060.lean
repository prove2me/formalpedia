-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_GraphAreaHolomorphic_proof_d91937b5f060
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:38:00.012798+00:00
-- url     : https://prove2.me/submissions/76b20cec-1210-4053-890d-ed6640606c5d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsArea
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StAreaMultiplicity
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGraphAreaHolomorphic
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PGraphAreaHolomorphic
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_GraphAreaHolomorphic_norm_sq_sumElim_309aed0fc72d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_GraphAreaHolomorphic_adjoint_comp_self_of_norm_406da87f1cbf
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_GraphAreaHolomorphic_det_one_add_comp_6312c74855cc
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_GraphAreaHolomorphic_differentiableAt_graphPt_real_10d051ea4057
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_GraphAreaHolomorphic_hasFDerivAt_graphPt_apply_4c54771741a3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_GraphAreaHolomorphic_exists_graph_isometry_16f89bb741a0
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MeasureTheory Module
open scoped ENNReal
noncomputable section
open GraphAreaHolomorphic
namespace GroundTheory.Heights₂.Heights
namespace GraphAreaHolomorphic
theorem _root_.solution (h : AreaGraph.Statement) : GraphAreaHolomorphic.Statement := by
  intro d m n e Ω F hΩ hF A hAΩ hA

  have hFcC : ContDiffOn ℂ 1 F Ω := by
    refine contDiffOn_piLp' 2 fun j x hx => ContDiffAt.contDiffWithinAt ?_
    have hU : IsOpen ((WithLp.toLp 2 : (Fin d → ℂ) → EuclideanSpace ℂ (Fin d)) ⁻¹' Ω) :=
      hΩ.preimage (PiLp.continuous_toLp 2 _)
    have hg : DifferentiableOn ℂ (fun w : Fin d → ℂ => F (WithLp.toLp 2 w) j)
        ((WithLp.toLp 2 : (Fin d → ℂ) → EuclideanSpace ℂ (Fin d)) ⁻¹' Ω) := fun w hw =>
      (((differentiableAt_piLp 2).1 (hF.differentiableAt (hΩ.mem_nhds hw)) j).comp w
        (PiLp.hasFDerivAt_toLp (𝕜 := ℂ) 2 w).differentiableAt).differentiableWithinAt
    exact ((ReciprocityTheory.AnForm.Osgood.osgood d _ _ hU hg (WithLp.ofLp x) hx).contDiffAt).comp x
      PiLp.contDiff_ofLp.contDiffAt
  have hFc : ContDiffOn ℝ 1 F Ω := hFcC.restrict_scalars ℝ
  have hd : finrank ℝ (EuclideanSpace ℂ (Fin d)) = 2 * d := by
    rw [finrank_real_of_complex, finrank_euclideanSpace_fin]
  have hm : finrank ℝ (EuclideanSpace ℂ (Fin m)) = 2 * m := by
    rw [finrank_real_of_complex, finrank_euclideanSpace_fin]
  obtain ⟨φ⟩ : Nonempty (EuclideanSpace ℂ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (2 * d))) :=
    ⟨((stdOrthonormalBasis ℝ _).reindex (finCongr hd)).repr⟩
  obtain ⟨φm⟩ : Nonempty (EuclideanSpace ℂ (Fin m) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (2 * m))) :=
    ⟨((stdOrthonormalBasis ℝ _).reindex (finCongr hm)).repr⟩
  obtain ⟨ψ, hψ, hψG⟩ := exists_graph_isometry e φ φm
  obtain ⟨F', hF'⟩ : ∃ F' : EuclideanSpace ℝ (Fin (2 * d)) → EuclideanSpace ℝ (Fin (2 * m)),
      F' = fun y => φm (F (φ.symm y)) := ⟨_, rfl⟩
  have hU : IsOpen (φ '' Ω) := φ.toHomeomorph.isOpenMap Ω hΩ
  have hA' : MeasurableSet (φ '' A) := φ.toHomeomorph.measurableEmbedding.measurableSet_image.2 hA
  have hF'c : ContDiffOn ℝ 1 F' (φ '' Ω) := by
    rw [hF']
    exact φm.toContinuousLinearEquiv.contDiff.comp_contDiffOn
      (hFc.comp φ.symm.toContinuousLinearEquiv.contDiff.contDiffOn
        (by rintro _ ⟨y, hy, rfl⟩; simpa using hy))
  have hmp : MeasurePreserving φ μH[((2 * d : ℕ) : ℝ)] μH[((2 * d : ℕ) : ℝ)] :=
    φ.toIsometryEquiv.measurePreserving_hausdorffMeasure _
  have himg : (fun x => ψ (graphPt e F x)) '' A = realGraphPt F' '' (φ '' A) := by
    rw [Set.image_image]
    refine Set.image_congr fun x _ => ?_
    rw [hψG, hF']
    simp [realGraphPt]
  rw [← hψ.hausdorffMeasure_image (Or.inl (Nat.cast_nonneg _)) (graphPt e F '' A), Set.image_image,
    himg, h (2 * d) (2 * m) (φ '' Ω) F' hU hF'c (φ '' A) (Set.image_mono hAΩ) hA',
    ← hmp.setLIntegral_comp_emb φ.toHomeomorph.measurableEmbedding]
  refine setLIntegral_congr_fun hA fun x hx => ?_
  have hFx : HasFDerivAt F (fderiv ℝ F x) x :=
    ((hF.differentiableAt (hΩ.mem_nhds (hAΩ hx))).restrictScalars ℝ).hasFDerivAt
  have hG : HasFDerivAt (graphPt e F) (fderiv ℝ (graphPt e F) x) x :=
    (differentiableAt_graphPt_real e hFx.differentiableAt).hasFDerivAt
  set K : EuclideanSpace ℝ (Fin (2 * d)) →L[ℝ] EuclideanSpace ℝ (Fin (2 * m)) :=
    (φm.toContinuousLinearEquiv : EuclideanSpace ℂ (Fin m) →L[ℝ] _).comp
      ((fderiv ℝ F x).comp (φ.symm.toContinuousLinearEquiv : EuclideanSpace ℝ (Fin (2 * d)) →L[ℝ] _))
    with hK
  have hF'x : HasFDerivAt F' K (φ x) := by
    rw [hF']
    exact φm.toContinuousLinearEquiv.hasFDerivAt.comp _
      ((by simpa using hFx : HasFDerivAt F (fderiv ℝ F x) (φ.symm (φ x))).comp _
        φ.symm.toContinuousLinearEquiv.hasFDerivAt)
  simp only [hF'x.fderiv, areaJacobian]
  congr 2
  rw [adjoint_comp_self_of_norm _
    ((K : EuclideanSpace ℝ (Fin (2 * d)) →ₗ[ℝ] EuclideanSpace ℝ (Fin (2 * m))) ∘ₗ φ.toLinearMap),
    det_one_add_comp]
  intro v
  simp only [ContinuousLinearMap.coe_coe]
  rw [hasFDerivAt_graphPt_apply e hFx hG v, norm_sq_sumElim]
  simp [hK]
end GraphAreaHolomorphic
end GroundTheory.Heights₂.Heights
