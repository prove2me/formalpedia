-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.schemeDifferentialRestrictionImageSectionIsoTo_congr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:04:51.153314+00:00
-- url     : https://prove2.me/submissions/6b5d8450-80e7-4b67-98f8-d35a00418977

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_SchemeSectionRestriction
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_SchemeRestrictionCoherence

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped _root_.AlgebraicGeometry
noncomputable section
universe u
variable {Y X : Scheme.{u}} (i j : Y ⟶ X)
variable [IsOpenImmersion i] [IsOpenImmersion j]
variable (k : CommRingCat.{u}) (c : k ⟶ Γ(X, ⊤)) (d : k ⟶ Γ(Y, ⊤))
variable (hi : schemeRestrictionConstantMap i k c = d)
variable (hj : schemeRestrictionConstantMap j k c = d)
local notation "OmegaX" => schemeDifferentialSheaf X k c
namespace QEC.Coding.AlgebraicGeometry
theorem _root_.solution
    (h : i = j) (U : Y.Opens) (s : Γ(schemeDifferentialSheaf Y k d, U)) :
    (schemeDifferentialRestrictionImageSectionIsoTo i k c d hi U).hom s =
    (OmegaX).presheaf.map (eqToHom (schemeOpenImmersionImage_congr i j h U)).op
      ((schemeDifferentialRestrictionImageSectionIsoTo j k c d hj U).hom s) := by
  subst j
  change (schemeDifferentialRestrictionImageSectionIsoTo i k c d hi U).hom s =
    (OmegaX).presheaf.map (𝟙 (op (i ''ᵁ U)))
      ((schemeDifferentialRestrictionImageSectionIsoTo i k c d hi U).hom s)
  exact (congrArg (fun t : Γ(OmegaX, i ''ᵁ U) ⟶ Γ(OmegaX, i ''ᵁ U) =>
    t ((schemeDifferentialRestrictionImageSectionIsoTo i k c d hi U).hom s))
      ((OmegaX).presheaf.map_id (op (i ''ᵁ U)))).symm
end QEC.Coding.AlgebraicGeometry
