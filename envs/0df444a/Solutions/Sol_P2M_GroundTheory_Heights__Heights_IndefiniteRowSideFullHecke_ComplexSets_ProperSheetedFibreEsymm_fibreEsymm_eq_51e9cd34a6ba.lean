-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_ProperSheetedFibreEsymm_fibreEsymm_eq_51e9cd34a6ba
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:23:12.580199+00:00
-- url     : https://prove2.me/submissions/8c6cec63-6a23-4e9c-bbcf-c6f548aec004

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StProperSheetedFibreEsymm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StUnbranchedProperCountConstant
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRiemannExtensionAnalytic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StParametricCircleIntegralAnalytic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PProperSheetedFibreEsymm

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
open Topology Filter Set Complex
open scoped Real
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.ProperSheetedFibreEsymm
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.ProperSheetedFibreEsymm
theorem _root_.solution {σ : Type} {d : ℕ} {Y : Set (σ → ℂ)} {A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)}
    {l : (σ → ℂ) →L[ℂ] ℂ} {j : ℕ} {t : Fin d → ℂ} (s : Finset (σ → ℂ))
    (hs : (↑s : Set (σ → ℂ)) = {x | x ∈ Y ∧ A x = t}) : fibreEsymm Y A l j t = (s.val.map l).esymm j := by
  have h : {x | x ∈ Y ∧ A x = t}.Finite := hs ▸ s.finite_toSet
  have hs' : h.toFinset = s := Finset.coe_injective (by rw [Set.Finite.coe_toFinset, hs])
  rw [fibreEsymm, dif_pos h, hs']
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.ProperSheetedFibreEsymm
