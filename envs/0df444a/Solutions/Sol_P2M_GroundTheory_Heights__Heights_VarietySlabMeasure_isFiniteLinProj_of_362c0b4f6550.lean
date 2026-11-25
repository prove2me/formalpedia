-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_VarietySlabMeasure_isFiniteLinProj_of_362c0b4f6550
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:22:57.889806+00:00
-- url     : https://prove2.me/submissions/27f9c00a-4689-4460-b50c-2c15a790117b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StVarietySlabMeasure
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StVarietyProjectionMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFiniteProjectionsGeneric
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_RingKrullDimQuotBotOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_AffineOfCone
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PNullSmaller
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFibreBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PVarietySlabMeasure

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
open MvPolynomial MeasureTheory
open scoped ENNReal
noncomputable section
open GroundTheory.Heights₂.Heights.VarietySlabMeasure
namespace GroundTheory.Heights₂.Heights.VarietySlabMeasure
theorem _root_.solution {n d : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)}
    {A : Matrix (Fin d) (Fin n) ℂ} (h : ComplexSets.IsFiniteProjection J A) :
    IsFiniteLinProj J A :=
  ⟨h.injective, h.finite⟩
end GroundTheory.Heights₂.Heights.VarietySlabMeasure
