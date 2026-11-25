-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_NormalGermIntegrallyClosed_analyticAt_of_differentiableOn_71078bf4599b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:29:29.213548+00:00
-- url     : https://prove2.me/submissions/40fb8e22-a32f-4559-a230-060b740ab13a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalGermIntegrallyClosed
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StZariskiAnalyticNormality
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRueckertNullstellensatz
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_OsgoodSeparate
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PNormalGermIntegrallyClosed
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open MvPolynomial Topology Filter
noncomputable section
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.NormalGermIntegrallyClosed
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.NormalGermIntegrallyClosed
theorem _root_.solution {σ : Type} [Fintype σ] {N : Set (σ → ℂ)} {f : (σ → ℂ) → ℂ}
    (hN : IsOpen N) (hf : DifferentiableOn ℂ f N) {z : σ → ℂ} (hz : z ∈ N) : AnalyticAt ℂ f z := by
  let L : (Fin (Fintype.card σ) → ℂ) ≃L[ℂ] (σ → ℂ) :=
    (LinearEquiv.funCongrLeft ℂ ℂ (Fintype.equivFin σ)).toContinuousLinearEquiv
  have hO : IsOpen (L ⁻¹' N) := hN.preimage L.continuous
  have hg : DifferentiableOn ℂ (f ∘ L) (L ⁻¹' N) :=
    hf.comp L.differentiable.differentiableOn fun x hx => hx
  have hA : AnalyticOnNhd ℂ (f ∘ L) (L ⁻¹' N) := by
    refine analyticOnNhd_of_continuousOn_of_separately hO hg.continuousOn fun x hx i => ?_
    have h1 : DifferentiableAt ℂ (f ∘ L) (Function.update x i (x i)) := by
      rw [Function.update_eq_self]
      exact hg.differentiableAt (hO.mem_nhds hx)
    exact h1.comp (x i) (hasFDerivAt_update x (x i)).differentiableAt
  have hz' : L.symm z ∈ L ⁻¹' N := by simpa using hz
  have h2 := (hA _ hz').comp ((L.symm : (σ → ℂ) →L[ℂ] (Fin (Fintype.card σ) → ℂ)).analyticAt z)
  simpa [Function.comp_def] using h2
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.NormalGermIntegrallyClosed
