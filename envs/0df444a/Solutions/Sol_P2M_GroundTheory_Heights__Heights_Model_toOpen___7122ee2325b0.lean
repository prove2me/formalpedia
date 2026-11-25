-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_toOpen___7122ee2325b0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:27:26.892577+00:00
-- url     : https://prove2.me/submissions/70fcfa65-40ea-402f-a2e4-e15ede45752d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsSpreadNbhd

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
theorem _root_.solution (f : X ⟶ SpecZ) (R : Type) [CommRing R] (W : X.Opens)
    (hW : Set.range (baseChangeMap f R) ⊆ Set.range W.ι) :
    toOpen f R W hW ≫ W.ι = baseChangeMap f R :=
  IsOpenImmersion.lift_fac _ _ _
end GroundTheory.Heights₂.Heights.Model
