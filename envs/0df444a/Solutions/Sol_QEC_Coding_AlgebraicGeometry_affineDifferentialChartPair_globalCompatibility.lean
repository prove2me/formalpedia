-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.affineDifferentialChartPair_globalCompatibility
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:25:22.400781+00:00
-- url     : https://prove2.me/submissions/88f73535-c1cf-4a90-a563-560840711fcd

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_AffineRestriction
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_ModulePairDescent
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_AffineChartDescent
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_affineDifferentialChartPair_of_imageCompatibility

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
    (z : Γ(Omega, ⊤)) (a : KaehlerDifferential k A) (b : KaehlerDifferential k C)
    (ha : (Omega).presheaf.map (homOfLE le_top : U ⟶ ⊤).op z = (E0).hom a)
    (hb : (Omega).presheaf.map (homOfLE le_top : V ⟶ ⊤).op z = (E1).hom b) :
    KaehlerDifferential.map k k A B a = KaehlerDifferential.map k k C B b := by
  apply affineDifferentialChartPair_of_imageCompatibility k A C B q r hq hr hqa hra
    f g c hf hg he a b
  have h0 : (Omega).presheaf.map
        (homOfLE (schemeNestedImage_le f (Spec.map q))).op ((E0).hom a) =
      (Omega).presheaf.map (homOfLE le_top : W ⟶ ⊤).op z := by
    have hr := congrArg (fun t : Γ(Omega, U) =>
      (Omega).presheaf.map (homOfLE (schemeNestedImage_le f (Spec.map q))).op t) ha.symm
    refine hr.trans ?_
    rw [← ConcreteCategory.comp_apply, ← (Omega).presheaf.map_comp]
    rfl
  have h1 : (Omega).presheaf.map
        (homOfLE ((eW).le.trans (schemeNestedImage_le g (Spec.map r)))).op ((E1).hom b) =
      (Omega).presheaf.map (homOfLE le_top : W ⟶ ⊤).op z := by
    have hr := congrArg (fun t : Γ(Omega, V) =>
      (Omega).presheaf.map
        (homOfLE ((eW).le.trans (schemeNestedImage_le g (Spec.map r)))).op t) hb.symm
    refine hr.trans ?_
    rw [← ConcreteCategory.comp_apply, ← (Omega).presheaf.map_comp]
    rfl
  exact h0.trans h1.symm
end QEC.Coding.AlgebraicGeometry
