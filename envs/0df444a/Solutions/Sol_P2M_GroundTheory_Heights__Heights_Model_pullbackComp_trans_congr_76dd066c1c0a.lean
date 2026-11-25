-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_pullbackComp_trans_congr_76dd066c1c0a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:06:19.043285+00:00
-- url     : https://prove2.me/submissions/a8f83443-aea3-424e-b439-85dcdb986a97

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_GlueCoherence

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
open CategoryTheory Limits AlgebraicGeometry
noncomputable section
set_option linter.unusedSimpArgs false
universe u
variable {T' T Y Z : Scheme.{u}}
namespace GroundTheory.Heights₂.Heights.Model
theorem _root_.solution (t : T' ⟶ T) {g : T ⟶ Y} {g' : T' ⟶ Y} (eg : t ≫ g = g')
    (F : Y.Modules) :
    (Scheme.Modules.pullbackComp t g).app F ≪≫ (Scheme.Modules.pullbackCongr eg).app F =
      (pullbackCompIso eg (Iso.refl ((Scheme.Modules.pullback g).obj F))).symm := by
  subst eg
  ext1
  simp [pullbackCompIso, Scheme.Modules.pullbackCongr]
end GroundTheory.Heights₂.Heights.Model
