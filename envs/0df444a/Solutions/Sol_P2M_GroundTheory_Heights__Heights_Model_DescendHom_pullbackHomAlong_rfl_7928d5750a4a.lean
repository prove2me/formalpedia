-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_DescendHom_pullbackHomAlong_rfl_7928d5750a4a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:26:06.647012+00:00
-- url     : https://prove2.me/submissions/af0ec299-1737-42d8-a250-788f5d8d1cf9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsDescendHom
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PClearDenominators
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PDescendHom

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
open GroundTheory.Heights₂.Heights.Model.DescendHom
variable {T Y Z : Scheme.{0}}
namespace GroundTheory.Heights₂.Heights.Model.DescendHom
theorem _root_.solution (ι : Z ⟶ Y) (g' : T ⟶ Z) {F G : Y.Modules}
    (ψ : (Scheme.Modules.pullback ι).obj F ⟶ (Scheme.Modules.pullback ι).obj G) :
    pullbackHomAlong (rfl : g' ≫ ι = g' ≫ ι) ψ = (Scheme.Modules.pullbackComp g' ι).inv.app F ≫
      (Scheme.Modules.pullback g').map ψ ≫ (Scheme.Modules.pullbackComp g' ι).hom.app G := by
  simp [pullbackHomAlong, pullbackCompIso, Scheme.Modules.pullbackCongr]
end GroundTheory.Heights₂.Heights.Model.DescendHom
