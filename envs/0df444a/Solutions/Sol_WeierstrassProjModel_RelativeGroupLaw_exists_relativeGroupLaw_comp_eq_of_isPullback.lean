-- Prove2me | solution 1 for WeierstrassProjModel.RelativeGroupLaw.exists_relativeGroupLaw_comp_eq_of_isPullback
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/7ca8cefd-aa4d-5f6b-81a4-6f00a1b343e2

import Mathlib
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassProjModel_RelativeGroupLaw_exists_relativeGroupLaw_comp_eq_of_isPullback

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory NeronModelInfra WeierstrassProjModel

namespace PullbackLawAux

variable {R R' : Type u} [CommRing R] [CommRing R'] {g : R →+* R'}
  {A A' : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} {f' : A' ⟶ Spec (CommRingCat.of R')}
  {π : A' ⟶ A} (hP : IsPullback π f' f (Spec.map (CommRingCat.ofHom g)))

def toG {S : Scheme.{u}} {s : S ⟶ Spec (CommRingCat.of R')} (x : SchemeHomOver s f') :
    SchemeHomOver (s ≫ Spec.map (CommRingCat.ofHom g)) f :=
  ⟨x.1 ≫ π, by rw [Category.assoc, hP.w, ← Category.assoc, x.2]⟩

noncomputable def ofG {S : Scheme.{u}} {s : S ⟶ Spec (CommRingCat.of R')}
    (x' : SchemeHomOver (s ≫ Spec.map (CommRingCat.ofHom g)) f) : SchemeHomOver s f' :=
  ⟨hP.lift x'.1 s x'.2, hP.lift_snd _ _ _⟩

@[scoped simp] lemma toG_coe {S : Scheme.{u}} {s : S ⟶ Spec (CommRingCat.of R')} (x : SchemeHomOver s f') :
    (toG hP x).1 = x.1 ≫ π := rfl

@[scoped simp] lemma ofG_coe_comp {S : Scheme.{u}} {s : S ⟶ Spec (CommRingCat.of R')}
    (x' : SchemeHomOver (s ≫ Spec.map (CommRingCat.ofHom g)) f) : (ofG hP x').1 ≫ π = x'.1 :=
  hP.lift_fst _ _ _

@[scoped simp] lemma toG_ofG {S : Scheme.{u}} {s : S ⟶ Spec (CommRingCat.of R')}
    (x' : SchemeHomOver (s ≫ Spec.map (CommRingCat.ofHom g)) f) : toG hP (ofG hP x') = x' :=
  Subtype.ext (hP.lift_fst _ _ _)

@[scoped simp] lemma ofG_toG {S : Scheme.{u}} {s : S ⟶ Spec (CommRingCat.of R')} (x : SchemeHomOver s f') :
    ofG hP (toG hP x) = x :=
  Subtype.ext (hP.hom_ext (by rw [ofG_coe_comp, toG_coe]) (by rw [(ofG hP (toG hP x)).2, x.2]))

lemma ofG_injective {S : Scheme.{u}} {s : S ⟶ Spec (CommRingCat.of R')}
    {x' y' : SchemeHomOver (s ≫ Spec.map (CommRingCat.ofHom g)) f} (h : ofG hP x' = ofG hP y') : x' = y' := by
  rw [← toG_ofG hP x', h, toG_ofG]

lemma toG_comp {S S' : Scheme.{u}} {s : S ⟶ Spec (CommRingCat.of R')} {s' : S' ⟶ Spec (CommRingCat.of R')}
    (ψ : S' ⟶ S) (hψ : ψ ≫ s = s') (x : SchemeHomOver s f') :
    schemeHomOverComp ψ (show ψ ≫ (s ≫ Spec.map (CommRingCat.ofHom g)) = s' ≫ Spec.map (CommRingCat.ofHom g) by
      rw [← Category.assoc, hψ]) (toG hP x) = toG hP (schemeHomOverComp ψ hψ x) :=
  Subtype.ext (by simp [schemeHomOverComp_coe])

lemma ofG_comp {S S' : Scheme.{u}} {s : S ⟶ Spec (CommRingCat.of R')} {s' : S' ⟶ Spec (CommRingCat.of R')}
    (ψ : S' ⟶ S) (hψ : ψ ≫ s = s') (x' : SchemeHomOver (s ≫ Spec.map (CommRingCat.ofHom g)) f) :
    schemeHomOverComp ψ hψ (ofG hP x') =
      ofG hP (schemeHomOverComp ψ (show ψ ≫ (s ≫ Spec.map (CommRingCat.ofHom g)) = s' ≫ Spec.map (CommRingCat.ofHom g) by
        rw [← Category.assoc, hψ]) x') := by
  apply Subtype.ext
  apply hP.hom_ext
  · rw [schemeHomOverComp_coe, Category.assoc, ofG_coe_comp, ofG_coe_comp, schemeHomOverComp_coe]
  · rw [(schemeHomOverComp ψ hψ (ofG hP x')).2, (ofG hP _).2]

noncomputable def law (G : RelativeGroupLaw R f) : RelativeGroupLaw R' f' where
  mul s x y := ofG hP (G.mul _ (toG hP x) (toG hP y))
  one s := ofG hP (G.one _)
  inv s x := ofG hP (G.inv _ (toG hP x))
  mul_assoc s x y z := by simp only [toG_ofG]; rw [G.mul_assoc]
  one_mul s x := by simp only [toG_ofG]; rw [G.one_mul, ofG_toG]
  mul_one s x := by simp only [toG_ofG]; rw [G.mul_one, ofG_toG]
  inv_mul_cancel s x := by simp only [toG_ofG]; rw [G.inv_mul_cancel]
  mul_natural s s' ψ hψ x y := by
    rw [ofG_comp, G.mul_natural _ _ ψ, toG_comp, toG_comp]

end PullbackLawAux
p2m_reactivate "P2MW.S_WeierstrassProjModel_RelativeGroupLaw_exists_relativeGroupLaw_comp_eq_of_isPullback.PullbackLawAux"

theorem solution
    {R R' : Type u} [CommRing R] [CommRing R'] (g : R →+* R')
    {A A' : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of R)) (f' : A' ⟶ Spec (CommRingCat.of R'))
    (π : A' ⟶ A) (hP : IsPullback π f' f (Spec.map (CommRingCat.ofHom g)))
    (G : RelativeGroupLaw R f) :
    ∃ G' : RelativeGroupLaw R' f',
      (∀ {S : Scheme.{u}} (s : S ⟶ Spec (CommRingCat.of R')) (x y : SchemeHomOver s f'),
        (G'.mul s x y).1 ≫ π =
          (G.mul (s ≫ Spec.map (CommRingCat.ofHom g))
            ⟨x.1 ≫ π, by rw [Category.assoc, hP.w, ← Category.assoc, x.2]⟩
            ⟨y.1 ≫ π, by rw [Category.assoc, hP.w, ← Category.assoc, y.2]⟩).1) ∧
      (∀ {S : Scheme.{u}} (s : S ⟶ Spec (CommRingCat.of R')),
        (G'.one s).1 ≫ π = (G.one (s ≫ Spec.map (CommRingCat.ofHom g))).1) := by
  refine ⟨PullbackLawAux.law hP G, ?_, ?_⟩
  · intro S s x y
    exact PullbackLawAux.ofG_coe_comp hP _
  · intro S s
    exact PullbackLawAux.ofG_coe_comp hP _

end S_WeierstrassProjModel_RelativeGroupLaw_exists_relativeGroupLaw_comp_eq_of_isPullback
end P2MW
export P2MW.S_WeierstrassProjModel_RelativeGroupLaw_exists_relativeGroupLaw_comp_eq_of_isPullback (solution)
