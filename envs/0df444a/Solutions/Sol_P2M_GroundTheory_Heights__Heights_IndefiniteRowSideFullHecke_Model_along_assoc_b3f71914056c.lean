-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_along_assoc_b3f71914056c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T06:32:47.519125+00:00
-- url     : https://prove2.me/submissions/6d2dc4b5-d2fe-460c-97c3-37188f54e777

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
theorem _root_.solution {p : T' ⟶ T} {g : T ⟶ Y} {h : Y ⟶ Z} {k : T ⟶ Z} {k' : T' ⟶ Z}
    (e : g ≫ h = k) (e' : p ≫ k = k') (e'' : (p ≫ g) ≫ h = k')
    (ψ : (Scheme.Modules.pullback h).obj F ≅ (Scheme.Modules.pullback h).obj G) :
    along e' (along e ψ) = along e'' ψ := by
  subst e e'
  ext1
  have a₁ := NatTrans.congr_app (Scheme.Modules.pseudofunctor_associativity p g h) F
  have a₂ := NatTrans.congr_app (Scheme.Modules.pseudofunctor_associativity p g h) G
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, eqToHom_app, Category.id_comp] at a₁ a₂
  have k₁ : (Scheme.Modules.pullbackComp p (g ≫ h)).inv.app F ≫
      (Scheme.Modules.pullback p).map ((Scheme.Modules.pullbackComp g h).inv.app F) =
      eqToHom (by simp) ≫ (Scheme.Modules.pullbackComp (p ≫ g) h).inv.app F ≫
        (Scheme.Modules.pullbackComp p g).inv.app ((Scheme.Modules.pullback h).obj F) := by
    rw [← cancel_mono ((Scheme.Modules.pullbackComp p g).hom.app ((Scheme.Modules.pullback h).obj F) ≫
      (Scheme.Modules.pullbackComp (p ≫ g) h).hom.app F)]
    simp only [Category.assoc] at a₁ ⊢
    rw [a₁]
    simp
  have k₂ : (Scheme.Modules.pullback p).map ((Scheme.Modules.pullbackComp g h).hom.app G) ≫
      (Scheme.Modules.pullbackComp p (g ≫ h)).hom.app G =
      (Scheme.Modules.pullbackComp p g).hom.app ((Scheme.Modules.pullback h).obj G) ≫
        (Scheme.Modules.pullbackComp (p ≫ g) h).hom.app G ≫ eqToHom (by simp) := by
    rw [← cancel_epi ((Scheme.Modules.pullbackComp p (g ≫ h)).inv.app G ≫
      (Scheme.Modules.pullback p).map ((Scheme.Modules.pullbackComp g h).inv.app G))]
    simp only [Category.assoc] at a₂ ⊢
    rw [reassoc_of% a₂]
    simp [← Functor.map_comp_assoc]
  have n := (Scheme.Modules.pullbackComp p g).hom.naturality ψ.hom
  simp only [Functor.comp_map] at n
  rw [along_hom, along_hom, along_hom]
  simp only [Scheme.Modules.pullbackCongr, eqToIso_refl, Iso.refl_inv, Iso.refl_hom,
    NatTrans.id_app, Category.id_comp, Category.comp_id, Functor.map_comp, Category.assoc]
  rw [reassoc_of% k₁, k₂, reassoc_of% n]
  simp
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model
