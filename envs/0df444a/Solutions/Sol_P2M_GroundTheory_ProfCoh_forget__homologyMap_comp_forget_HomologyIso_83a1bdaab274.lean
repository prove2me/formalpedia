-- Prove2me | solution 1 for P2M_GroundTheory_ProfCoh_forget__homologyMap_comp_forget_HomologyIso_83a1bdaab274
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:43:21.201005+00:00
-- url     : https://prove2.me/submissions/402a1e80-f04f-4b9d-a3b2-c3dc4d77012a

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalClassFormation_FiniteVanishing_IntScalars

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.ProfCoh
open CategoryTheory Limits groupCohomology
variable {Γ : Type} [Group Γ]
namespace GroundTheory.ProfCoh
theorem _root_.solution
    {S₁ T₁ : ShortComplex (ModuleCat.{0} (ULift.{0} ℤ))} {S₂ T₂ : ShortComplex (ModuleCat.{0} ℤ)}
    (φ₁ : S₁ ⟶ T₁) (φ₂ : S₂ ⟶ T₂)
    (σS : (forget₂ (ModuleCat.{0} (ULift.{0} ℤ)) Ab).mapShortComplex.obj S₁ ≅
      (forget₂ (ModuleCat.{0} ℤ) Ab).mapShortComplex.obj S₂)
    (σT : (forget₂ (ModuleCat.{0} (ULift.{0} ℤ)) Ab).mapShortComplex.obj T₁ ≅
      (forget₂ (ModuleCat.{0} ℤ) Ab).mapShortComplex.obj T₂)
    (h : (forget₂ (ModuleCat.{0} (ULift.{0} ℤ)) Ab).mapShortComplex.map φ₁ ≫ σT.hom =
      σS.hom ≫ (forget₂ (ModuleCat.{0} ℤ) Ab).mapShortComplex.map φ₂) :
    (ShortComplex.homologyFunctor _ ⋙ forget₂ (ModuleCat.{0} (ULift.{0} ℤ)) Ab).map φ₁ ≫
        (forget₂HomologyIso σT).hom =
      (forget₂HomologyIso σS).hom ≫
        (ShortComplex.homologyFunctor _ ⋙ forget₂ (ModuleCat.{0} ℤ) Ab).map φ₂ := by
  have n1 := (ShortComplex.homologyFunctorIso (forget₂ (ModuleCat.{0} (ULift.{0} ℤ)) Ab)).inv.naturality φ₁
  have n2 := (ShortComplex.homologyFunctorIso (forget₂ (ModuleCat.{0} ℤ) Ab)).hom.naturality φ₂
  have n3 : ((forget₂ (ModuleCat.{0} (ULift.{0} ℤ)) Ab).mapShortComplex ⋙
        ShortComplex.homologyFunctor Ab).map φ₁ ≫ (ShortComplex.homologyFunctor Ab).map σT.hom =
      (ShortComplex.homologyFunctor Ab).map σS.hom ≫
        ((forget₂ (ModuleCat.{0} ℤ) Ab).mapShortComplex ⋙ ShortComplex.homologyFunctor Ab).map φ₂ := by
    rw [Functor.comp_map, Functor.comp_map, ← Functor.map_comp, ← Functor.map_comp, h]
  simp only [forget₂HomologyIso, Iso.trans_hom, Iso.symm_hom, Iso.app_inv, Iso.app_hom,
    Functor.mapIso_hom, Category.assoc]
  slice_lhs 1 2 => rw [n1]
  slice_lhs 2 3 => rw [n3]
  slice_lhs 3 4 => rw [n2]
end GroundTheory.ProfCoh
