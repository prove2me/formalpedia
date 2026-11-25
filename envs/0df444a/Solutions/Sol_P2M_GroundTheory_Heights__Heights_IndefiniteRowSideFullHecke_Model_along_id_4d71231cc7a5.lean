-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_along_id_4d71231cc7a5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T06:32:51.407151+00:00
-- url     : https://prove2.me/submissions/18c09987-983d-4106-acaf-a92e25fec916

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
theorem _root_.solution {g : Y ⟶ Y} {h : Y ⟶ Z} (hg : g = 𝟙 Y) (e : g ≫ h = h)
    (ψ : (Scheme.Modules.pullback h).obj F ≅ (Scheme.Modules.pullback h).obj G) :
    along e ψ = ψ := by
  subst hg
  ext1
  have h₁ := NatTrans.congr_app (Scheme.Modules.pseudofunctor_right_unitality h) F
  have h₂ := NatTrans.congr_app (Scheme.Modules.pseudofunctor_right_unitality h) G
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.rightUnitor_hom_app,
    eqToHom_app] at h₁ h₂
  erw [Category.comp_id] at h₁ h₂
  have k₁ : (Scheme.Modules.pullbackComp (𝟙 Y) h).inv.app F =
      eqToHom (by simp) ≫ (Scheme.Modules.pullbackId Y).inv.app ((Scheme.Modules.pullback h).obj F) := by
    rw [← h₁]; simp
  have k₂ : (Scheme.Modules.pullbackComp (𝟙 Y) h).hom.app G =
      (Scheme.Modules.pullbackId Y).hom.app ((Scheme.Modules.pullback h).obj G) ≫ eqToHom (by simp) := by
    rw [← cancel_epi ((Scheme.Modules.pullbackComp (𝟙 Y) h).inv.app G), ← Category.assoc, h₂]
    simp
  have n := (Scheme.Modules.pullbackId Y).hom.naturality ψ.hom
  simp only [Functor.id_map] at n
  rw [along_hom, k₁, k₂]
  simp only [Category.assoc]
  rw [reassoc_of% n]
  simp [Scheme.Modules.pullbackCongr]
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model
