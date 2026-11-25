-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_along_hom_46c147a3a660
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T06:09:40.925086+00:00
-- url     : https://prove2.me/submissions/2cd5f018-cb56-4869-ac7d-d330234d72d8

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_IsIsoPullbackObjUnitToUnit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_SpreadIsoModelIff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model
open CategoryTheory AlgebraicGeometry
variable {T T' Y Z : Scheme.{0}} {F G : Z.Modules}
local notation "along" => GroundTheory.Heights₂.Heights.Model.pullbackIsoAlong
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model
theorem _root_.solution {g : T ⟶ Y} {h : Y ⟶ Z} {k : T ⟶ Z} (e : g ≫ h = k)
    (ψ : (Scheme.Modules.pullback h).obj F ≅ (Scheme.Modules.pullback h).obj G) :
    (along e ψ).hom = (Scheme.Modules.pullbackCongr e).inv.app F ≫
      (Scheme.Modules.pullbackComp g h).inv.app F ≫ (Scheme.Modules.pullback g).map ψ.hom ≫
        (Scheme.Modules.pullbackComp g h).hom.app G ≫ (Scheme.Modules.pullbackCongr e).hom.app G := by
  simp [GroundTheory.Heights₂.Heights.Model.pullbackIsoAlong, GroundTheory.Heights₂.Heights.Model.pullbackCompIso]
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model
