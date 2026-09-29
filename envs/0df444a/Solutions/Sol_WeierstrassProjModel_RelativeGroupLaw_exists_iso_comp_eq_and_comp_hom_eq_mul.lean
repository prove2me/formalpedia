-- Prove2me | solution 1 for WeierstrassProjModel.RelativeGroupLaw.exists_iso_comp_eq_and_comp_hom_eq_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/5632a84a-52be-5681-ae80-4a8d4ac774f0

import Mathlib
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassProjModel_RelativeGroupLaw_exists_iso_comp_eq_and_comp_hom_eq_mul

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra WeierstrassProjModel

namespace A1Body

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra WeierstrassProjModel

universe v

variable {R : Type v} [CommRing R] {A : Scheme.{v}} {f : A ⟶ Spec (CommRingCat.of R)}

noncomputable def transl (G : RelativeGroupLaw R f) (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f) : A ⟶ A :=
  (G.mul f RelativeGroupLaw.idPoint (schemeHomOverComp f (Category.comp_id f) P)).1

theorem transl_over (G : RelativeGroupLaw R f) (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f) :
    transl G P ≫ f = f :=
  (G.mul f RelativeGroupLaw.idPoint (schemeHomOverComp f (Category.comp_id f) P)).2

theorem comp_transl (G : RelativeGroupLaw R f) (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f)
    {X : Scheme.{v}} (t : X ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f) :
    x.1 ≫ transl G P = (G.mul t x (schemeHomOverComp t (Category.comp_id t) P)).1 := by
  have hx : x.1 ≫ f = t := x.2
  have key := G.mul_natural f t x.1 hx RelativeGroupLaw.idPoint (schemeHomOverComp f (Category.comp_id f) P)
  have lhs : (schemeHomOverComp x.1 hx (G.mul f RelativeGroupLaw.idPoint (schemeHomOverComp f (Category.comp_id f) P))).1
      = x.1 ≫ transl G P := rfl
  have h1 : schemeHomOverComp x.1 hx (RelativeGroupLaw.idPoint (f := f)) = x := by
    apply Subtype.ext
    simp [schemeHomOverComp_coe]
  have h2 : schemeHomOverComp x.1 hx (schemeHomOverComp f (Category.comp_id f) P)
      = schemeHomOverComp t (Category.comp_id t) P := by
    apply Subtype.ext
    simp only [schemeHomOverComp_coe]
    rw [← Category.assoc, hx]
  rw [← lhs, key, h1, h2]

theorem transl_comp_transl (G : RelativeGroupLaw R f) (P Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f) :
    transl G P ≫ transl G Q =
      (G.mul f RelativeGroupLaw.idPoint
        (G.mul f (schemeHomOverComp f (Category.comp_id f) P) (schemeHomOverComp f (Category.comp_id f) Q))).1 := by
  have h := comp_transl G Q f (G.mul f RelativeGroupLaw.idPoint (schemeHomOverComp f (Category.comp_id f) P))
  change transl G P ≫ transl G Q = _ at h
  rw [h, G.mul_assoc]

theorem comp_inv (G : RelativeGroupLaw R f) (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f) :
    schemeHomOverComp f (Category.comp_id f) (G.inv _ P) = G.inv f (schemeHomOverComp f (Category.comp_id f) P) := by
  letI : Group (SchemeHomOver f f) := G.pointGroup f
  have hm := G.mul_natural (𝟙 _) f f (Category.comp_id f) (G.inv _ P) P
  rw [G.inv_mul_cancel, G.one_natural] at hm
  have h1 : schemeHomOverComp f (Category.comp_id f) (G.inv _ P) * schemeHomOverComp f (Category.comp_id f) P = 1 :=
    hm.symm
  exact eq_inv_of_mul_eq_one_left h1

theorem transl_mul_inv (G : RelativeGroupLaw R f) (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f) :
    transl G P ≫ transl G (G.inv _ P) = 𝟙 A := by
  rw [transl_comp_transl, comp_inv]
  letI : Group (SchemeHomOver f f) := G.pointGroup f
  have h : G.mul f (schemeHomOverComp f (Category.comp_id f) P) (G.inv f (schemeHomOverComp f (Category.comp_id f) P))
      = G.one f := mul_inv_cancel (schemeHomOverComp f (Category.comp_id f) P)
  rw [h, G.mul_one]

theorem transl_inv_mul (G : RelativeGroupLaw R f) (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f) :
    transl G (G.inv _ P) ≫ transl G P = 𝟙 A := by
  rw [transl_comp_transl, comp_inv, G.inv_mul_cancel, G.mul_one]

end A1Body

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra WeierstrassProjModel in
theorem solution
    {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (G : RelativeGroupLaw R f) (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f) :
    ∃ τ : A ≅ A,
      τ.hom ≫ f = f ∧
      ∀ {X : Scheme.{u}} (t : X ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f),
        x.1 ≫ τ.hom = (G.mul t x (schemeHomOverComp t (Category.comp_id t) P)).1 := by
  refine ⟨⟨A1Body.transl G P, A1Body.transl G (G.inv _ P), A1Body.transl_mul_inv G P, A1Body.transl_inv_mul G P⟩,
    A1Body.transl_over G P, ?_⟩
  intro X t x
  exact A1Body.comp_transl G P t x

end S_WeierstrassProjModel_RelativeGroupLaw_exists_iso_comp_eq_and_comp_hom_eq_mul
end P2MW
export P2MW.S_WeierstrassProjModel_RelativeGroupLaw_exists_iso_comp_eq_and_comp_hom_eq_mul (solution)
