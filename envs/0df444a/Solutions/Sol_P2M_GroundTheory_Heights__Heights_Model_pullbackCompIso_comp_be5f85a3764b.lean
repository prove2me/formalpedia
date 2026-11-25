-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_pullbackCompIso_comp_be5f85a3764b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:06:17.57649+00:00
-- url     : https://prove2.me/submissions/028e9f5e-ed4d-458e-b3b9-0aaf61294151

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
theorem _root_.solution (t : T' ⟶ T) {g : T ⟶ Y} {h : Y ⟶ Z} {k : T ⟶ Z} (e : g ≫ h = k)
    {g' : T' ⟶ Y} (eg : t ≫ g = g') {k' : T' ⟶ Z} (ek : t ≫ k = k') (e' : g' ≫ h = k')
    {E : Z.Modules} {F : Y.Modules} (γ : (Scheme.Modules.pullback h).obj E ≅ F) :
    pullbackCompIso e' γ = pullbackCompIso ek (pullbackCompIso e γ) ≪≫
      (Scheme.Modules.pullbackComp t g).app F ≪≫ (Scheme.Modules.pullbackCongr eg).app F := by
  subst eg ek e
  ext1
  have assoc := congr_arg (fun φ => φ.app E)
    (Scheme.Modules.pseudofunctor_associativity t g h)
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.whiskerLeft_app, Category.id_comp, eqToHom_app] at assoc
  have nat := (Scheme.Modules.pullbackComp t g).hom.naturality γ.hom
  simp only [Functor.comp_map] at nat
  simp only [pullbackCompIso, Scheme.Modules.pullbackCongr, Iso.trans_hom, Iso.symm_hom, Iso.app_inv,
    eqToIso_refl, Iso.refl_inv, NatTrans.id_app, Functor.mapIso_hom, Iso.app_hom,
    Functor.map_comp, Category.assoc, Category.id_comp, eqToIso.inv, eqToIso.hom, eqToHom_app,
    eqToHom_refl, Category.comp_id, Functor.mapIso_trans, Functor.mapIso_symm, Iso.trans_assoc]
  simp only [Functor.mapIso_inv, Iso.app_inv, Iso.app_hom, Iso.refl_inv, Iso.refl_hom,
    NatTrans.id_app, Functor.map_id, Category.id_comp, Category.comp_id]
  simp only [CategoryTheory.Functor.map_id, Category.id_comp]
  rw [nat]
  have assoc' : (Scheme.Modules.pullbackComp t (g ≫ h)).inv.app E ≫
      (Scheme.Modules.pullback t).map ((Scheme.Modules.pullbackComp g h).inv.app E) ≫
        (Scheme.Modules.pullbackComp t g).hom.app ((Scheme.Modules.pullback h).obj E) =
      eqToHom (by rw [Category.assoc]) ≫ (Scheme.Modules.pullbackComp (t ≫ g) h).inv.app E := by
    rw [← cancel_mono ((Scheme.Modules.pullbackComp (t ≫ g) h).hom.app E)]
    simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
    exact assoc
  slice_rhs 2 3 => erw [Category.id_comp]
  slice_rhs 1 3 => rw [assoc']
  simp only [Category.assoc]
end GroundTheory.Heights₂.Heights.Model
