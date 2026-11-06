-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.affineDifferentialChartPair_of_imageCompatibility
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:20:41.920178+00:00
-- url     : https://prove2.me/submissions/c54a25e2-208b-41d1-892d-eb67089553cf

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_AffineRestriction
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_ModulePairDescent
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_AffineChartDescent
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_additiveSectionIso_hom_injective
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_affineDifferentialChartImageKaehlerIso_restrict
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_schemeDifferentialRestrictionImageSectionIsoTo_congr
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_schemeModuleNestedImageRestriction
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_schemeModuleRestriction_cast


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped _root_.AlgebraicGeometry
noncomputable section
universe u
variable (k : Type u) (A C B : CommRingCat.{u}) [CommRing k]
variable [Algebra k A] [Algebra k C] [Algebra k B]
variable [Algebra A B] [Algebra C B] [IsScalarTower k A B] [IsScalarTower k C B]
variable (q : A ⟶ B) (r : C ⟶ B)
variable (hq : ∀ a : A, q a = algebraMap A B a)
variable (hr : ∀ a : C, r a = algebraMap C B a)
variable (hqa : (CommRingCat.ofHom (algebraMap k A) : CommRingCat.of k ⟶ A) ≫ q =
  CommRingCat.ofHom (algebraMap k B))
variable (hra : (CommRingCat.ofHom (algebraMap k C) : CommRingCat.of k ⟶ C) ≫ r =
  CommRingCat.ofHom (algebraMap k B))
variable {X : Scheme.{u}} (f : Spec A ⟶ X) (g : Spec C ⟶ X)
variable [IsOpenImmersion (Spec.map q)] [IsOpenImmersion (Spec.map r)]
variable [IsOpenImmersion f] [IsOpenImmersion g]
variable (c : CommRingCat.of k ⟶ Γ(X, ⊤))
variable (hf : schemeRestrictionConstantMap f (CommRingCat.of k) c =
  affineDifferentialGlobalConstantMap k A)
variable (hg : schemeRestrictionConstantMap g (CommRingCat.of k) c =
  affineDifferentialGlobalConstantMap k C)
variable (he : Spec.map q ≫ f = Spec.map r ≫ g)
local notation "Omega" => schemeDifferentialSheaf X (CommRingCat.of k) c
local notation "U" => Functor.obj (Scheme.Hom.opensFunctor f) ⊤
local notation "V" => Functor.obj (Scheme.Hom.opensFunctor g) ⊤
local notation "W" => Functor.obj (Scheme.Hom.opensFunctor (Spec.map q ≫ f)) ⊤
local notation "W1" => Functor.obj (Scheme.Hom.opensFunctor (Spec.map r ≫ g)) ⊤
local notation "E0" => affineDifferentialChartImageKaehlerIso k A f c hf
local notation "E1" => affineDifferentialChartImageKaehlerIso k C g c hg
local notation "eW" => schemeOpenImmersionImage_congr
  (Spec.map q ≫ f) (Spec.map r ≫ g) he ⊤
local notation "hc0" => schemeRestrictionConstantMap_comp_to f (Spec.map q) (CommRingCat.of k) c
  (affineDifferentialGlobalConstantMap k A) (affineDifferentialGlobalConstantMap k B)
  hf (affineDifferentialRestrictionConstantMap k A B q hqa)
local notation "hc1" => schemeRestrictionConstantMap_comp_to g (Spec.map r) (CommRingCat.of k) c
  (affineDifferentialGlobalConstantMap k C) (affineDifferentialGlobalConstantMap k B)
  hg (affineDifferentialRestrictionConstantMap k C B r hra)
local notation "F0" => schemeDifferentialRestrictionImageSectionIsoTo (Spec.map q ≫ f)
  (CommRingCat.of k) c (affineDifferentialGlobalConstantMap k B) hc0 ⊤
local notation "F1" => schemeDifferentialRestrictionImageSectionIsoTo (Spec.map r ≫ g)
  (CommRingCat.of k) c (affineDifferentialGlobalConstantMap k B) hc1 ⊤
local notation "EB" => affineDifferentialGlobalSectionsEquiv k B
include hq hr hqa hra he
namespace QEC.Coding.AlgebraicGeometry
theorem _root_.solution
    (a : KaehlerDifferential k A) (b : KaehlerDifferential k C)
    (hcompat : (Omega).presheaf.map
        (homOfLE (schemeNestedImage_le f (Spec.map q))).op ((E0).hom a) =
      (Omega).presheaf.map
        (homOfLE ((eW).le.trans (schemeNestedImage_le g (Spec.map r)))).op ((E1).hom b)) :
    KaehlerDifferential.map k k A B a = KaehlerDifferential.map k k C B b := by
  have h0 := affineDifferentialChartImageKaehlerIso_restrict k A B q hqa hq f c hf a
  have h1 := affineDifferentialChartImageKaehlerIso_restrict k C B r hra hr g c hg b
  have hn0 : (Omega).presheaf.map (homOfLE (schemeNestedImage_le f (Spec.map q))).op
      ((E0).hom a) = (F0).hom ((EB).symm (KaehlerDifferential.map k k A B a)) :=
    (schemeModuleNestedImageRestriction f (Spec.map q) Omega ((E0).hom a)).symm.trans h0
  have hn1 : (Omega).presheaf.map (homOfLE (schemeNestedImage_le g (Spec.map r))).op
      ((E1).hom b) = (F1).hom ((EB).symm (KaehlerDifferential.map k k C B b)) :=
    (schemeModuleNestedImageRestriction g (Spec.map r) Omega ((E1).hom b)).symm.trans h1
  have hs := schemeDifferentialRestrictionImageSectionIsoTo_congr
    (Spec.map q ≫ f) (Spec.map r ≫ g) (CommRingCat.of k) c
    (affineDifferentialGlobalConstantMap k B) hc0 hc1 he ⊤
      ((EB).symm (KaehlerDifferential.map k k C B b))
  have hcast := schemeModuleRestriction_cast Omega eW
    (schemeNestedImage_le g (Spec.map r)) ((E1).hom b)
  have hn1' := congrArg (fun z : Γ(Omega, W1) =>
    (Omega).presheaf.map (eqToHom eW).op z) hn1
  have hE : (F0).hom ((EB).symm (KaehlerDifferential.map k k A B a)) =
      (F0).hom ((EB).symm (KaehlerDifferential.map k k C B b)) :=
    hn0.symm.trans (hcompat.trans (hcast.symm.trans (hn1'.trans hs.symm)))
  exact (EB).symm.injective (additiveSectionIso_hom_injective F0 hE)
end QEC.Coding.AlgebraicGeometry
