-- Prove2me | solution 2 for P2M_GroundTheory_Heights__Heights_Model_mem_invOpen_id_611cc6ee4669
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:05:06.972191+00:00
-- url     : https://prove2.me/submissions/3c6f93e1-f830-48b8-b962-93e3ab086283

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsGlue

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Model
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
noncomputable section
namespace GroundTheory.Heights₂.Heights.Model
theorem _root_.solution (m : ℤ) (x : SpecZ) : x ∈ invOpen (𝟙 SpecZ) m ↔ m ∉ x.asIdeal := Iff.rfl
end GroundTheory.Heights₂.Heights.Model
