-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_NormalGermIntegrallyClosed_toGerm_surjective_5df4007014f9
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:29:27.846852+00:00
-- url     : https://prove2.me/submissions/aca23ed7-69ac-46d7-9c4c-e8ba5c3eeff6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalGermIntegrallyClosed
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StZariskiAnalyticNormality
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRueckertNullstellensatz
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_OsgoodSeparate
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PNormalGermIntegrallyClosed

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
theorem _root_.solution {σ : Type} [Fintype σ] (w : σ → ℂ) : Function.Surjective (toGerm w) := by
  rintro ⟨φ, f, hf, rfl⟩
  exact ⟨⟨f, hf⟩, rfl⟩
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.NormalGermIntegrallyClosed
