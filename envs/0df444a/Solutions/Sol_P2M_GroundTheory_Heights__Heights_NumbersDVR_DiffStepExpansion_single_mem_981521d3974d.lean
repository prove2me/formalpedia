-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_DiffStepExpansion_single_mem_981521d3974d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:38:11.888692+00:00
-- url     : https://prove2.me/submissions/03d566ab-661c-4c7d-a9e8-b137018158a4

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsCN
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDiffStepExpansion

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
noncomputable section
open GroundTheory.Heights₂.Heights.NumbersDVR.DiffStepExpansion
variable {K : Type}
namespace GroundTheory.Heights₂.Heights.NumbersDVR.DiffStepExpansion
theorem _root_.solution [DecidableEq K] (k : K) : (Pi.single k 1 : K → ℤ) ∈ expandable K :=
  ⟨[((k, 0), 1)], fun f => by funext m; simp [expand, shiftFn]⟩
end GroundTheory.Heights₂.Heights.NumbersDVR.DiffStepExpansion
