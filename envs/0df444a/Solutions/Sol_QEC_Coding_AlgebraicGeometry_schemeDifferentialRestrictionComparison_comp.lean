-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.schemeDifferentialRestrictionComparison_comp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:09:14.439104+00:00
-- url     : https://prove2.me/submissions/c23d39b9-5435-4985-80e0-a8aec8b72c7b

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_SchemeSectionRestriction
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_SchemeRestrictionCoherence
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_schemeDifferentialRestrictionComparisonTo_D
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_schemeDifferentialRestrictionIso_derivation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_schemeDifferentialSheafDerivation_postcomp


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped _root_.AlgebraicGeometry
noncomputable section
universe u
variable {Y X Z : Scheme.{u}} (f : Y ⟶ X) (g : Z ⟶ Y)
variable [IsOpenImmersion f] [IsOpenImmersion g]
variable (k : CommRingCat.{u}) (c : k ⟶ Γ(X, ⊤))
local notation "cY" => schemeRestrictionConstantMap f k c
local notation "cZ" => schemeRestrictionConstantMap g k cY
local notation "OmegaX" => schemeDifferentialSheaf X k c
local notation "OmegaY" => schemeDifferentialSheaf Y k cY
local notation "OmegaZ" => schemeDifferentialSheaf Z k cZ
namespace QEC.Coding.AlgebraicGeometry
theorem _root_.solution :
    schemeDifferentialRestrictionComparisonTo (g ≫ f) k c cZ
      (schemeRestrictionConstantMap_comp f g k c) =
    schemeDifferentialRestrictionComparisonComposite f g k c := by
  apply (schemeDifferentialSheafHomEquiv Z k cZ
    ((Scheme.Modules.restrictFunctor (g ≫ f)).obj OmegaX)).injective
  rw [← schemeDifferentialSheafDerivation_postcomp,
    ← schemeDifferentialSheafDerivation_postcomp]
  ext U a
  change (schemeDifferentialRestrictionComparisonTo (g ≫ f) k c cZ
      (schemeRestrictionConstantMap_comp f g k c)).app U.unop
        ((schemeDifferentialSheafDerivation Z k cZ).d a) =
    (schemeDifferentialRestrictionComparisonComposite f g k c).app U.unop
      ((schemeDifferentialSheafDerivation Z k cZ).d a)
  have hdirect := schemeDifferentialRestrictionComparisonTo_D (g ≫ f) k c cZ
    (schemeRestrictionConstantMap_comp f g k c) U.unop a
  refine hdirect.trans ?_
  change (schemeDifferentialSheafDerivation X k c).d
      (((g ≫ f).appIso U.unop).inv a) =
    ((Scheme.Modules.restrictFunctorComp g f).inv.app OmegaX).app U.unop
      ((schemeDifferentialRestrictionComparison f k c).app (g ''ᵁ U.unop)
        ((schemeDifferentialRestrictionComparison g k cY).app U.unop
          ((schemeDifferentialSheafDerivation Z k cZ).d a)))
  have hg := PresheafOfModules.Derivation.congr_d
    (schemeDifferentialRestrictionIso_derivation g k cY) (X := U) a
  have hgf := congrArg (fun z : Γ(OmegaY, g ''ᵁ U.unop) =>
    (schemeDifferentialRestrictionComparison f k c).app (g ''ᵁ U.unop) z) hg
  have hf := PresheafOfModules.Derivation.congr_d
    (schemeDifferentialRestrictionIso_derivation f k c) (X := op (g ''ᵁ U.unop))
      ((g.appIso U.unop).inv a)
  have hright := congrArg (fun z : Γ(OmegaX, f ''ᵁ (g ''ᵁ U.unop)) =>
    ((Scheme.Modules.restrictFunctorComp g f).inv.app OmegaX).app U.unop z) (hgf.trans hf)
  refine (Eq.trans ?_ hright.symm)
  rw [Scheme.Modules.restrictFunctorComp_inv_app_app]
  have hr := congrArg (fun e : Γ(X, (g ≫ f) ''ᵁ U.unop) ≅ Γ(Z, U.unop) => e.inv a)
    (Scheme.Hom.comp_appIso g f U.unop)
  have hd := (schemeDifferentialSheafDerivation X k c).d_map
    (eqToHom (Scheme.Hom.comp_image g f U.unop)).op
      ((f.appIso (g ''ᵁ U.unop)).inv ((g.appIso U.unop).inv a))
  exact (congrArg (fun z : Γ(X, (g ≫ f) ''ᵁ U.unop) =>
    (schemeDifferentialSheafDerivation X k c).d (X := op ((g ≫ f) ''ᵁ U.unop)) z) hr).trans hd
end QEC.Coding.AlgebraicGeometry
