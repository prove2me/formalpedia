-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.schemeDifferentialRestrictionComparisonTo_D
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:06:21.363735+00:00
-- url     : https://prove2.me/submissions/dec459a9-da7e-444b-98ce-e147d2dad766

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_SchemeSectionRestriction
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_SchemeRestrictionCoherence
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_schemeDifferentialRestrictionIso_derivation


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
    {W V : Scheme.{u}} (i : W ⟶ V) [IsOpenImmersion i]
    (b : CommRingCat.{u}) (a : b ⟶ Γ(V, ⊤)) (d : b ⟶ Γ(W, ⊤))
    (h : schemeRestrictionConstantMap i b a = d) (U : W.Opens) (x : Γ(W, U)) :
    (schemeDifferentialRestrictionComparisonTo i b a d h).app U
      ((schemeDifferentialSheafDerivation W b d).d (X := op U) x) =
    (schemeDifferentialSheafDerivation V b a).d (X := op (i ''ᵁ U))
      ((i.appIso U).inv x) := by
  subst d
  exact PresheafOfModules.Derivation.congr_d
    (schemeDifferentialRestrictionIso_derivation i b a) (X := op U) x
end QEC.Coding.AlgebraicGeometry
