-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_MultiHomogPrimeCriterion_lexDeg_injective_d0613a591d1a
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:43:48.197517+00:00
-- url     : https://prove2.me/submissions/b3d52f90-93eb-41ee-baa3-2a875dee7b36

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsCN
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PMultiHomogPrimeCriterion

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
noncomputable section
universe u
open GroundTheory.Heights₂.Heights.NumbersDVR.MultiHomogPrimeCriterion
variable {K : Type} [Fintype K] [DecidableEq K]
omit [DecidableEq K]
namespace GroundTheory.Heights₂.Heights.NumbersDVR.MultiHomogPrimeCriterion
theorem _root_.solution : Function.Injective (lexDeg (K := K)) := by
  intro a b h
  funext k
  have := congrFun (congrArg ofLex h) (Fintype.equivFin K k)
  change a ((Fintype.equivFin K).symm (Fintype.equivFin K k)) =
    b ((Fintype.equivFin K).symm (Fintype.equivFin K k)) at this
  simpa using this
end GroundTheory.Heights₂.Heights.NumbersDVR.MultiHomogPrimeCriterion
