-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_SectionNefGenerated_of_sectionNef_d5327fdbf2e3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:05:01.535483+00:00
-- url     : https://prove2.me/submissions/554c9c1d-1a9d-4e52-a18d-b43659fd6bf3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_BundleObjects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements

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
namespace SectionNefGenerated
theorem _root_.solution (h : SectionNef.Statement) :
    SectionNefGenerated.Statement := by
  intro K _ _ ι _ F _ P hP hd b hb
  obtain ⟨f, g, hs, -⟩ := hb P hP le_rfl
  exact h K ι F P hP hd b f g hs
end SectionNefGenerated
end GroundTheory.Heights₂.Heights.Model
