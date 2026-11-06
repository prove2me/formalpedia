-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.affineDifferentialChartImageKaehlerIso_restrict
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:19:20.034695+00:00
-- url     : https://prove2.me/submissions/7dd91cf7-8add-456c-9a44-a8c943d8d30b

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_SchemeRestrictionCoherence
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_AffineDifferentials
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_AffineRestriction
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_affineDifferentialGlobalRestriction_inverseEquiv
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_schemeDifferentialRestrictionImageSectionIsoTo_globalRestriction


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped _root_.AlgebraicGeometry
noncomputable section
universe u
variable (k : Type u) (A B : CommRingCat.{u}) [CommRing k]
variable [Algebra k A] [Algebra k B] [Algebra A B] [IsScalarTower k A B]
variable (q : A ⟶ B)
variable (hcoeff : (CommRingCat.ofHom (algebraMap k A) : CommRingCat.of k ⟶ A) ≫ q =
  (CommRingCat.ofHom (algebraMap k B) : CommRingCat.of k ⟶ B))
variable [IsOpenImmersion (Spec.map q)]
variable (hq : ∀ a : A, q a = algebraMap A B a)
variable {X : Scheme.{u}} (f : Spec A ⟶ X) [IsOpenImmersion f]
variable (c : CommRingCat.of k ⟶ Γ(X, ⊤))
variable (hf : schemeRestrictionConstantMap f (CommRingCat.of k) c =
  affineDifferentialGlobalConstantMap k A)
local notation "OmegaX" => schemeDifferentialSheaf X (CommRingCat.of k) c
local notation "OmegaA" => schemeDifferentialSheaf (Spec A) (CommRingCat.of k)
  (affineDifferentialGlobalConstantMap k A)
local notation "OmegaB" => schemeDifferentialSheaf (Spec B) (CommRingCat.of k)
  (affineDifferentialGlobalConstantMap k B)
include hq
namespace QEC.Coding.AlgebraicGeometry
theorem _root_.solution (s : KaehlerDifferential k A) :
    (OmegaX).presheaf.map (eqToHom (Scheme.Hom.comp_image (Spec.map q) f ⊤)).op
      ((OmegaX).presheaf.map
        (f.opensFunctor.map (homOfLE le_top : Spec.map q ''ᵁ ⊤ ⟶ ⊤)).op
          ((affineDifferentialChartImageKaehlerIso k A f c hf).hom s)) =
    (schemeDifferentialRestrictionImageSectionIsoTo (Spec.map q ≫ f) (CommRingCat.of k) c
      (affineDifferentialGlobalConstantMap k B)
      (schemeRestrictionConstantMap_comp_to f (Spec.map q) (CommRingCat.of k) c
        (affineDifferentialGlobalConstantMap k A) (affineDifferentialGlobalConstantMap k B)
        hf (affineDifferentialRestrictionConstantMap k A B q hcoeff)) ⊤).hom
          ((affineDifferentialGlobalSectionsEquiv k B).symm
            (KaehlerDifferential.map k k A B s)) := by
  have hn := (schemeDifferentialRestrictionImageSectionIsoTo_globalRestriction
    f (Spec.map q) (CommRingCat.of k) c
      (affineDifferentialGlobalConstantMap k A) (affineDifferentialGlobalConstantMap k B)
      hf (affineDifferentialRestrictionConstantMap k A B q hcoeff)
      ((affineDifferentialGlobalSectionsEquiv k A).symm s)).symm
  exact hn.trans (congrArg (fun z : Γ(OmegaB, ⊤) =>
    (schemeDifferentialRestrictionImageSectionIsoTo (Spec.map q ≫ f) (CommRingCat.of k) c
      (affineDifferentialGlobalConstantMap k B)
      (schemeRestrictionConstantMap_comp_to f (Spec.map q) (CommRingCat.of k) c
        (affineDifferentialGlobalConstantMap k A) (affineDifferentialGlobalConstantMap k B)
        hf (affineDifferentialRestrictionConstantMap k A B q hcoeff)) ⊤).hom z)
    (affineDifferentialGlobalRestriction_inverseEquiv k A B q hcoeff hq s))
end QEC.Coding.AlgebraicGeometry
