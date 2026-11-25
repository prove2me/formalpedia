-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_differentiableAt_graphPt_1c88044ce855
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:31:44.473705+00:00
-- url     : https://prove2.me/submissions/fffce8ee-d663-4718-ad92-1d9fab7d924b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsArea
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StAreaMultiplicity
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFrameJacobianSum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGraphAreaHolomorphic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PProjectionFormula

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
theorem _root_.solution {d m n : ℕ} (e : Fin n ≃ Fin d ⊕ Fin m)
    {F : EuclideanSpace ℂ (Fin d) → EuclideanSpace ℂ (Fin m)} {x : EuclideanSpace ℂ (Fin d)}
    (hF : DifferentiableAt ℂ F x) : DifferentiableAt ℂ (graphPt e F) x := by
  rw [differentiableAt_piLp]
  intro j
  show DifferentiableAt ℂ (fun y => Sum.elim (fun i => y i) (fun i => F y i) (e j)) x
  rcases hj : e j with i | i
  · simp only [Sum.elim_inl]
    exact (differentiableAt_piLp 2).1 differentiableAt_id i
  · simp only [Sum.elim_inr]
    exact (differentiableAt_piLp 2).1 hF i
end GroundTheory.Heights₂.Heights
