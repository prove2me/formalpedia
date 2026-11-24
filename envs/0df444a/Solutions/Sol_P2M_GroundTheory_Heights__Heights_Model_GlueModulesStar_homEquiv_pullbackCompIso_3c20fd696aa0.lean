-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_GlueModulesStar_homEquiv_pullbackCompIso_3c20fd696aa0
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:33:14.772831+00:00
-- url     : https://prove2.me/submissions/6bb58460-338f-4391-9245-1e998d219ea3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsGlue
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PGlueModulesStar

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
open GroundTheory.Heights₂.Heights.Model.GlueModulesStar
universe u
open Scheme.Modules
namespace GroundTheory.Heights₂.Heights.Model.GlueModulesStar
theorem _root_.solution {T Y Z : Scheme.{u}} {g : T ⟶ Y} {h : Y ⟶ Z} {k : T ⟶ Z}
    (e : g ≫ h = k) {E : Z.Modules} {F : Y.Modules} (γ : (Scheme.Modules.pullback h).obj E ≅ F) {M : T.Modules}
    (χ : (Scheme.Modules.pullback g).obj F ⟶ M) :
    (pullbackPushforwardAdjunction k).homEquiv _ _ ((pullbackCompIso e γ).hom ≫ χ) =
      (pullbackPushforwardAdjunction h).homEquiv _ _ γ.hom ≫ transMap g h e χ := by
  subst e
  have hc1 : (pullbackCongr (rfl : g ≫ h = g ≫ h)).inv.app E = 𝟙 _ := by
    simp [pullbackCongr]
  have hc2 : (pushforwardCongr (rfl : g ≫ h = g ≫ h)).hom.app M = 𝟙 _ := by
    ext O : 1
    exact M.presheaf.map_id _
  have key : ∀ (φ : (Scheme.Modules.pullback g).obj ((Scheme.Modules.pullback h).obj E) ⟶ M),
      (pullbackPushforwardAdjunction (g ≫ h)).homEquiv _ _ ((pullbackComp g h).inv.app E ≫ φ) =
        ((pullbackPushforwardAdjunction h).comp (pullbackPushforwardAdjunction g)).homEquiv _ _ φ ≫
          (pushforwardComp g h).hom.app M := by
    intro φ
    have hu := unit_conjugateEquiv
      ((pullbackPushforwardAdjunction h).comp (pullbackPushforwardAdjunction g))
      (pullbackPushforwardAdjunction (g ≫ h)) (pullbackComp g h).inv E
    rw [conjugateEquiv_pullbackComp_inv] at hu
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc,
      ← hu, Category.assoc, Category.assoc]
    congr 1
  simp only [pullbackCompIso, Iso.trans_hom, Iso.symm_hom, Iso.app_inv, Functor.mapIso_hom,
    Category.assoc, hc1, Category.id_comp, key, transMap, hc2, Category.comp_id,
    Adjunction.comp_homEquiv, Equiv.trans_apply]
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right, Category.assoc]
end GroundTheory.Heights₂.Heights.Model.GlueModulesStar
