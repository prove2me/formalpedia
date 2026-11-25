-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_germQuotPointIdeal_le_jacobson_60b0c1ad5c75
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:48:10.641327+00:00
-- url     : https://prove2.me/submissions/df63eb20-0a18-47a8-aa90-51db683f5839

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StHolGermsNoetherian
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCompletionNormalDescent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StAffineCompletionNormal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGermCompletionEquiv
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PZariskiAnalyticNormality
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_holGermPointIdeal_le_jacobson_b6948958a3dc

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
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
theorem _root_.solution {σ : Type} [Fintype σ] (I : Ideal (MvPolynomial σ ℂ)) (w : σ → ℂ) :
    germQuotPointIdeal I w ≤ (⊥ : Ideal (holGerms w ⧸ I.map (polyGerm w))).jacobson := by
  intro x hx
  obtain ⟨x', hx', rfl⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 hx
  rw [Ideal.mem_jacobson_bot]
  intro y
  obtain ⟨y', rfl⟩ := Ideal.Quotient.mk_surjective y
  have hu := Ideal.mem_jacobson_bot.1 (holGermPointIdeal_le_jacobson w hx') y'
  simpa [map_add, map_mul] using hu.map (Ideal.Quotient.mk (I.map (polyGerm w)))
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
