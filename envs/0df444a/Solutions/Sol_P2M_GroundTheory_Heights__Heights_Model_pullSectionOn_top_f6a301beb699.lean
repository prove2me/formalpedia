-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_pullSectionOn_top_f6a301beb699
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:06:16.780795+00:00
-- url     : https://prove2.me/submissions/2f8f9623-8b66-426f-8941-7ca09c058b6a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PullbackBasis

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
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
noncomputable section
universe u
namespace GroundTheory.Heights₂.Heights.Model
theorem _root_.solution {T Z : Scheme.{u}} (g : T ⟶ Z) (M : Z.Modules) :
    pullSectionOn g M ⊤ = pullSection g M := rfl
end GroundTheory.Heights₂.Heights.Model
