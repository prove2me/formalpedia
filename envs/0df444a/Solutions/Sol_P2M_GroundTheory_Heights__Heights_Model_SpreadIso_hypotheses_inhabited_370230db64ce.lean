-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_SpreadIso_hypotheses_inhabited_370230db64ce
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:05:09.963204+00:00
-- url     : https://prove2.me/submissions/b4fac69c-f34d-4728-a604-6661ca00295f

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
namespace SpreadIso
theorem _root_.solution :
    IsVectorBundle (structureModule (invOpen (𝟙 SpecZ) (1 : ℕ) : Scheme.{0})) ∧
      Nonempty ((Scheme.Modules.pullback (toInvOpen (𝟙 SpecZ) ℚ (1 : ℕ)
        (isUnit_intCast_rat 1 one_ne_zero))).obj (structureModule _) ≅
        (Scheme.Modules.pullback (toInvOpen (𝟙 SpecZ) ℚ (1 : ℕ)
        (isUnit_intCast_rat 1 one_ne_zero))).obj (structureModule _)) :=
  ⟨isVectorBundle_structureModule, ⟨Iso.refl _⟩⟩
end SpreadIso
end GroundTheory.Heights₂.Heights.Model
