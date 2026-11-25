-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_invOpen_le_of_dvd__4378c74e8fc8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:05:15.824106+00:00
-- url     : https://prove2.me/submissions/d3c5f9b7-fd05-4f2d-927d-2841f24905b1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsGlue
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_GlueCoherence
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PGlueBundles

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
variable {X : Scheme.{0}}
namespace GroundTheory.Heights₂.Heights.Model
theorem _root_.solution (f : X ⟶ SpecZ) {a b : ℤ} (h : a ∣ b) : invOpen f b ≤ invOpen f a := by
  obtain ⟨c, rfl⟩ := h
  exact invOpen_mul_le_left f a c
end GroundTheory.Heights₂.Heights.Model
