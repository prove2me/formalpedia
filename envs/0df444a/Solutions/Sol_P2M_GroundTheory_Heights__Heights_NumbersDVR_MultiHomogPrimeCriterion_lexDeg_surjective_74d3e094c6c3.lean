-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_MultiHomogPrimeCriterion_lexDeg_surjective_74d3e094c6c3
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:43:48.312776+00:00
-- url     : https://prove2.me/submissions/6bba43dc-0b69-4c8f-9073-3c42ced60617

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
theorem _root_.solution : Function.Surjective (lexDeg (K := K)) := by
  intro i
  refine ⟨fun k => ofLex i (Fintype.equivFin K k), ?_⟩
  show toLex _ = i
  rw [← toLex_ofLex i]
  congr 1
  funext j
  simp
end GroundTheory.Heights₂.Heights.NumbersDVR.MultiHomogPrimeCriterion
