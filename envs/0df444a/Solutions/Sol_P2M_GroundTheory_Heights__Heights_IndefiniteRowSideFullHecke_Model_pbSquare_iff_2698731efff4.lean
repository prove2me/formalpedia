-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_pbSquare_iff_2698731efff4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:14:59.166381+00:00
-- url     : https://prove2.me/submissions/df6de4d1-5cde-4ecd-89e5-0ab48ceaabe0

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_IsIsoPullbackObjUnitToUnit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_SpreadIsoModelIff
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_along_hom_46c147a3a660

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
theorem _root_.solution {A B C : Scheme.{0}} (q : A ⟶ B) (j : B ⟶ Z) (k : A ⟶ C) (r : C ⟶ Z)
    (hsq : q ≫ j = k ≫ r) (f : (Scheme.Modules.pullback j).obj F ≅ (Scheme.Modules.pullback j).obj G)
    (ψ : (Scheme.Modules.pullback r).obj F ≅ (Scheme.Modules.pullback r).obj G) :
    (Scheme.Modules.pullback q).map f.hom = (pbSquare q j k r hsq F).hom ≫
        (Scheme.Modules.pullback k).map ψ.hom ≫ (pbSquare q j k r hsq G).inv ↔
      along hsq f = along (rfl : k ≫ r = k ≫ r) ψ := by
  constructor
  · intro H
    ext1
    rw [along_hom, along_hom, H]
    simp [pbSquare, Scheme.Modules.pullbackCongr]
  · intro H
    have key : (Scheme.Modules.pullback q).map f.hom =
        (Scheme.Modules.pullbackComp q j).hom.app F ≫ (Scheme.Modules.pullbackCongr hsq).hom.app F ≫
          (along hsq f).hom ≫ (Scheme.Modules.pullbackCongr hsq).inv.app G ≫
            (Scheme.Modules.pullbackComp q j).inv.app G := by
      rw [along_hom]; simp
    rw [key, H, along_hom]
    simp [pbSquare, Scheme.Modules.pullbackCongr]
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model
