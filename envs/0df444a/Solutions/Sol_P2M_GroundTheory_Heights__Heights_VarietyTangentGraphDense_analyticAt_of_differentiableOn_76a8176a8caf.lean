-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_VarietyTangentGraphDense_analyticAt_of_differentiableOn_76a8176a8caf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:29:18.715439+00:00
-- url     : https://prove2.me/submissions/8abfb2e8-b89e-4b86-8b15-3028300fae60

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StVarietyTangentGraphDense
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StZeroSetOpenMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_StFramePlaneGraph
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PFramePlaneGraph
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PFrameGraphGeneric
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PFrameJacobianGeneric
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PJacobianRankGeneric
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PConormalGenerationGeneric
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PFrameImplicitGraph
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PNullSmaller
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_OsgoodSeparate
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PVarietyTangentGraphDense
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_analyticOnNhd_of_continuousOn_of_separately_ff52795ca853


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
open MvPolynomial Topology Filter MeasureTheory
noncomputable section
open GroundTheory.Heights₂.Heights.VarietyTangentGraphDense
namespace GroundTheory.Heights₂.Heights.VarietyTangentGraphDense
theorem _root_.solution {σ : Type} [Fintype σ] {m : ℕ} {U : Set (σ → ℂ)}
    {G : (σ → ℂ) → EuclideanSpace ℂ (Fin m)} (hU : IsOpen U) (hG : DifferentiableOn ℂ G U) {w : σ → ℂ}
    (hw : w ∈ U) : AnalyticAt ℂ G w := by
  classical
  let e : σ ≃ Fin (Fintype.card σ) := Fintype.equivFin σ
  let E : (Fin (Fintype.card σ) → ℂ) ≃L[ℂ] (σ → ℂ) :=
    ContinuousLinearEquiv.piCongrLeft ℂ (fun _ : σ => ℂ) e.symm
  let P : EuclideanSpace ℂ (Fin m) ≃L[ℂ] (Fin m → ℂ) := PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin m => ℂ)
  let H : (Fin (Fintype.card σ) → ℂ) → Fin m → ℂ := fun y => P (G (E y))
  have hV : IsOpen (E ⁻¹' U) := hU.preimage E.continuous
  have hH : DifferentiableOn ℂ H (E ⁻¹' U) :=
    P.differentiable.comp_differentiableOn
      (hG.comp E.differentiable.differentiableOn (Set.mapsTo_preimage _ _))
  have hHa : AnalyticOnNhd ℂ H (E ⁻¹' U) := by
    intro y hy
    refine AnalyticAt.pi fun s => ?_
    have hs : DifferentiableOn ℂ (fun x => H x s) (E ⁻¹' U) :=
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin m => ℂ) s).differentiable.comp_differentiableOn hH
    refine IndefiniteRowSideFullHecke.ComplexSets.analyticOnNhd_of_continuousOn_of_separately hV hs.continuousOn
      (fun x hx i => ?_) y hy
    have h1 : DifferentiableAt ℂ (fun x => H x s) (Function.update x i (x i)) := by
      rw [Function.update_eq_self]
      exact hs.differentiableAt (hV.mem_nhds hx)
    exact h1.comp (x i) (hasFDerivAt_update (𝕜 := ℂ) x (x i)).differentiableAt
  have hGe : G = fun x => P.symm (H (E.symm x)) := by
    funext x
    simp [H]
  have hy : E.symm w ∈ E ⁻¹' U := by simpa using hw
  have hEa : AnalyticAt ℂ (⇑E.symm) w := by
    simpa using (E.symm : (σ → ℂ) →L[ℂ] (Fin (Fintype.card σ) → ℂ)).analyticAt w
  have hPa : AnalyticAt ℂ (⇑P.symm) (H (E.symm w)) := by
    simpa using (P.symm : (Fin m → ℂ) →L[ℂ] EuclideanSpace ℂ (Fin m)).analyticAt (H (E.symm w))
  rw [hGe]
  exact (hPa.comp (hHa _ hy)).comp hEa
end GroundTheory.Heights₂.Heights.VarietyTangentGraphDense
