-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.schemeDifferentialRestrictionImageSectionIso_naturality
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:09:21.256613+00:00
-- url     : https://prove2.me/submissions/ecf6fcc8-4613-4737-bf41-8c6e3a23e24d

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_SchemeSectionRestriction
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_SchemeRestrictionCoherence

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
theorem _root_.solution
    {U V : Y.Opens} (i : U ⟶ V) (s : Γ(OmegaY, V)) :
    (schemeDifferentialRestrictionImageSectionIso f k c U).hom
      ((OmegaY).presheaf.map i.op s) =
    (OmegaX).presheaf.map (f.opensFunctor.map i).op
      ((schemeDifferentialRestrictionImageSectionIso f k c V).hom s) :=
  congrArg (fun t => t s)
    (((Scheme.Modules.toPresheaf Y).map (schemeDifferentialRestrictionIso f k c).hom).naturality
      i.op)
end QEC.Coding.AlgebraicGeometry
