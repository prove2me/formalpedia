-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_SpreadBundle_hypotheses_inhabited_4ad4a2995cf0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:05:03.608218+00:00
-- url     : https://prove2.me/submissions/59ad9ddc-bbd2-49d6-bf72-2add0c9c33df

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_BundleObjects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_isVectorBundle_structureModule_93a0cef3461d

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
open NumbersDVR ReciprocityTheory.ChartRestriction.G.Geo
namespace GroundTheory.Heights₂.Heights.Model
namespace SpreadBundle
theorem _root_.solution :
    IsVectorBundle (structureModule (baseChange (𝟙 SpecZ) (ZLoc ⟨2, Nat.prime_two⟩))) :=
  isVectorBundle_structureModule
end SpreadBundle
end GroundTheory.Heights₂.Heights.Model
