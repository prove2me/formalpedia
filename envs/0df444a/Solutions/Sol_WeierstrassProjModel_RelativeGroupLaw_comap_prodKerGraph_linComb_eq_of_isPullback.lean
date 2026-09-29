-- Prove2me | solution 1 for WeierstrassProjModel.RelativeGroupLaw.comap_prodKerGraph_linComb_eq_of_isPullback
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/a59b0ac1-1e87-551c-8a7e-236c5e63518f

import Mathlib
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_WeierstrassCurve_DrinfeldBasisRelative
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_isPullback_projMap_of_isCoefficientHom
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_comap_mul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassProjModel_RelativeGroupLaw_comap_prodKerGraph_linComb_eq_of_isPullback

set_option autoImplicit false

universe u

p2m_open "AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal P2MW.S_WeierstrassProjModel_RelativeGroupLaw_comap_prodKerGraph_linComb_eq_of_isPullback.WeierstrassCurve.DrinfeldGlobal"

attribute [local instance] MvPolynomial.gradedAlgebra

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "map"
namespace DrinfeldGlobal
namespace BasisDivComap
p2m_open "WeierstrassCurve.DrinfeldGlobal WeierstrassCurve"

p2m_open "AlgebraicGeometry.Scheme"

theorem comap_prod {X Y : Scheme.{u}} (θ : X ⟶ Y) {ι : Type*} (s : Finset ι) (I : ι → Y.IdealSheafData) :
    (∏ i ∈ s, I i).comap θ = ∏ i ∈ s, (I i).comap θ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Scheme.IdealSheafData.comap_top]
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha, AlgebraicGeometry.Scheme.IdealSheafData.comap_mul, ih]

theorem ker_comp_iso_hom {X Y Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (e : X ≅ Y) :
    (i ≫ e.hom).ker = i.ker.comap e.inv := by
  rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion]
  have h : pullback.fst e.inv i = pullback.snd e.inv i ≫ i ≫ e.hom := by
    rw [← Category.assoc, ← pullback.condition, Category.assoc, e.inv_hom_id, Category.comp_id]
  rw [h]
  exact (Scheme.Hom.ker_comp_of_isIso _ _).symm

section Generic

variable {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}

theorem one_val (G : RelativeGroupLaw R f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    (G.one t).1 = t ≫ (G.one (𝟙 _)).1 := by
  rw [← G.one_natural (𝟙 _) t t (Category.comp_id t)]
  rfl

end Generic

theorem main
    {B T : Type u} [CommRing B] [CommRing T] (f : B →+* T)
    {E E' : Scheme.{u}} (p : E ⟶ Spec (CommRingCat.of B)) (p' : E' ⟶ Spec (CommRingCat.of T))
    [IsSeparated p] [IsSeparated p'] (π : E' ⟶ E)
    (hsq : π ≫ p = p' ≫ Spec.map (CommRingCat.ofHom f))
    (hK2 : IsPullback π p' p (Spec.map (CommRingCat.ofHom f)))
    (G : RelativeGroupLaw B p) (L : RelativeGroupLaw T p')
    (hmul : ∀ {S : Scheme.{u}} (s : S ⟶ Spec (CommRingCat.of T)) (x y : SchemeHomOver s p'),
      (L.mul s x y).1 ≫ π =
        (G.mul (s ≫ Spec.map (CommRingCat.ofHom f))
          ⟨x.1 ≫ π, by rw [Category.assoc, hsq, ← Category.assoc, x.2]⟩
          ⟨y.1 ≫ π, by rw [Category.assoc, hsq, ← Category.assoc, y.2]⟩).1)
    (hone : (L.one (𝟙 (Spec (CommRingCat.of T)))).1 ≫ π =
      Spec.map (CommRingCat.ofHom f) ≫ (G.one (𝟙 (Spec (CommRingCat.of B)))).1)
    (q : ℕ) (P Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of T))) p')
    (hP : (P.1 ≫ π) ≫ p = Spec.map (CommRingCat.ofHom f))
    (hQ : (Q.1 ≫ π) ≫ p = Spec.map (CommRingCat.ofHom f)) :
    Scheme.IdealSheafData.comap
      (prodKerGraph p
        (fun i : Fin (q * q) ↦ (G.mul (Spec.map (CommRingCat.ofHom f))
          (G.nsmul _ (i.val / q) ⟨P.1 ≫ π, hP⟩) (G.nsmul _ (i.val % q) ⟨Q.1 ≫ π, hQ⟩)).1)
        (fun i ↦ (G.mul (Spec.map (CommRingCat.ofHom f))
          (G.nsmul _ (i.val / q) ⟨P.1 ≫ π, hP⟩) (G.nsmul _ (i.val % q) ⟨Q.1 ≫ π, hQ⟩)).2))
      (pullback.lift (pullback.fst p' (𝟙 _) ≫ π) (pullback.snd p' (𝟙 _))
        (by rw [Category.assoc, hsq, ← Category.assoc, pullback.condition, Category.assoc, Category.id_comp])) =
      prodKerGraph p'
        (fun i : Fin (q * q) ↦ (L.mul (𝟙 _) (L.nsmul _ (i.val / q) P) (L.nsmul _ (i.val % q) Q)).1)
        (fun i ↦ (L.mul (𝟙 _) (L.nsmul _ (i.val / q) P) (L.nsmul _ (i.val % q) Q)).2) := by

  have hone' : ∀ {S : Scheme.{u}} (s : S ⟶ Spec (CommRingCat.of T)),
      (L.one s).1 ≫ π = (G.one (s ≫ Spec.map (CommRingCat.ofHom f))).1 := by
    intro S s
    rw [one_val L s, one_val G (s ≫ _), Category.assoc, hone, Category.assoc]
  have hnsmul : ∀ {S : Scheme.{u}} (s : S ⟶ Spec (CommRingCat.of T)) (x : SchemeHomOver s p') (n : ℕ),
      (L.nsmul s n x).1 ≫ π = (G.nsmul (s ≫ Spec.map (CommRingCat.ofHom f)) n
        ⟨x.1 ≫ π, by rw [Category.assoc, hsq, ← Category.assoc, x.2]⟩).1 := by
    intro S s x n
    induction n with
    | zero => exact hone' s
    | succ n ih =>
        rw [RelativeGroupLaw.nsmul_succ, RelativeGroupLaw.nsmul_succ, hmul]
        congr 2
        exact Subtype.ext ih

  have reidx : ∀ (z : SchemeHomOver (Spec.map (CommRingCat.ofHom f)) p),
      schemeHomOverComp (𝟙 _) rfl z =
        (⟨𝟙 _ ≫ z.1, by rw [Category.assoc, z.2]⟩ :
          SchemeHomOver (𝟙 _ ≫ Spec.map (CommRingCat.ofHom f)) p) := fun z ↦ rfl
  have tuple_eq : ∀ (a b : ℕ),
      (G.mul (Spec.map (CommRingCat.ofHom f)) (G.nsmul _ a ⟨P.1 ≫ π, hP⟩) (G.nsmul _ b ⟨Q.1 ≫ π, hQ⟩)).1 =
        (L.mul (𝟙 _) (L.nsmul _ a P) (L.nsmul _ b Q)).1 ≫ π := by
    intro a b
    rw [hmul]
    have eP : (⟨(L.nsmul (𝟙 _) a P).1 ≫ π, by rw [Category.assoc, hsq, ← Category.assoc, (L.nsmul (𝟙 _) a P).2]⟩ :
        SchemeHomOver (𝟙 _ ≫ Spec.map (CommRingCat.ofHom f)) p) =
        schemeHomOverComp (𝟙 _) rfl (G.nsmul _ a ⟨P.1 ≫ π, hP⟩) := by
      apply Subtype.ext
      change (L.nsmul (𝟙 _) a P).1 ≫ π = (schemeHomOverComp (𝟙 _) rfl (G.nsmul _ a ⟨P.1 ≫ π, hP⟩)).1
      rw [hnsmul, G.nsmul_natural]
      congr 2
    have eQ : (⟨(L.nsmul (𝟙 _) b Q).1 ≫ π, by rw [Category.assoc, hsq, ← Category.assoc, (L.nsmul (𝟙 _) b Q).2]⟩ :
        SchemeHomOver (𝟙 _ ≫ Spec.map (CommRingCat.ofHom f)) p) =
        schemeHomOverComp (𝟙 _) rfl (G.nsmul _ b ⟨Q.1 ≫ π, hQ⟩) := by
      apply Subtype.ext
      change (L.nsmul (𝟙 _) b Q).1 ≫ π = (schemeHomOverComp (𝟙 _) rfl (G.nsmul _ b ⟨Q.1 ≫ π, hQ⟩)).1
      rw [hnsmul, G.nsmul_natural]
      congr 2
    rw [eP, eQ, ← G.mul_natural]
    exact (Category.id_comp _).symm

  set Θ := pullback.lift (pullback.fst p' (𝟙 _) ≫ π) (pullback.snd p' (𝟙 _))
        (by rw [Category.assoc, hsq, ← Category.assoc, pullback.condition, Category.assoc, Category.id_comp]) with hΘ
  have hΘeq : Θ = pullback.fst p' (𝟙 _) ≫ hK2.isoPullback.hom := by
    apply pullback.hom_ext
    · rw [hΘ, pullback.lift_fst, Category.assoc, IsPullback.isoPullback_hom_fst]
    · rw [hΘ, pullback.lift_snd, Category.assoc, IsPullback.isoPullback_hom_snd, pullback.condition,
        Category.comp_id]
  haveI : IsIso Θ := by rw [hΘeq]; infer_instance
  have graph_eq : ∀ (a : Spec (CommRingCat.of T) ⟶ E') (ha : a ≫ p' = 𝟙 _)
      (ha' : (a ≫ π) ≫ p = Spec.map (CommRingCat.ofHom f)),
      graphOver p' a ha ≫ Θ = graphOver p (a ≫ π) ha' := by
    intro a ha ha'
    apply pullback.hom_ext
    · rw [Category.assoc, hΘ, pullback.lift_fst, ← Category.assoc, graphOver_fst, graphOver_fst]
    · rw [Category.assoc, hΘ, pullback.lift_snd, graphOver_snd, graphOver_snd]
  have ker_eq : ∀ (a : Spec (CommRingCat.of T) ⟶ E') (ha : a ≫ p' = 𝟙 _)
      (ha' : (a ≫ π) ≫ p = Spec.map (CommRingCat.ofHom f)),
      (graphOver p (a ≫ π) ha').ker.comap Θ = (graphOver p' a ha).ker := by
    intro a ha ha'
    rw [← graph_eq a ha ha', show Θ = (asIso Θ).hom from rfl, ker_comp_iso_hom, ← Scheme.IdealSheafData.comap_comp,
      (asIso Θ).hom_inv_id, Scheme.IdealSheafData.comap_id]
  have gcongr : ∀ {a a' : Spec (CommRingCat.of T) ⟶ E} (h : a = a') (ha : a ≫ p = Spec.map (CommRingCat.ofHom f))
      (ha' : a' ≫ p = Spec.map (CommRingCat.ofHom f)), graphOver p a ha = graphOver p a' ha' := by
    rintro _ _ rfl _ _; rfl
  rw [prodKerGraph, prodKerGraph, comap_prod]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  have := ker_eq ((L.mul (𝟙 _) (L.nsmul _ (i.val / q) P) (L.nsmul _ (i.val % q) Q)).1)
    ((L.mul (𝟙 _) (L.nsmul _ (i.val / q) P) (L.nsmul _ (i.val % q) Q)).2)
    (by rw [← tuple_eq]; exact (G.mul _ _ _).2)
  exact (congrArg (fun g ↦ Scheme.IdealSheafData.comap (Scheme.Hom.ker g) Θ) (gcongr (tuple_eq _ _) _ _)).trans this

end WeierstrassCurve.DrinfeldGlobal.BasisDivComap

open WeierstrassCurve.DrinfeldGlobal.BasisDivComap in
theorem solution
    {B T : Type u} [CommRing B] [CommRing T] (f : B →+* T)
    {E E' : Scheme.{u}} (p : E ⟶ Spec (CommRingCat.of B)) (p' : E' ⟶ Spec (CommRingCat.of T))
    [IsSeparated p] [IsSeparated p'] (π : E' ⟶ E)
    (hP : IsPullback π p' p (Spec.map (CommRingCat.ofHom f)))
    (G : RelativeGroupLaw B p) (L : RelativeGroupLaw T p')
    (hmul : ∀ {S : Scheme.{u}} (s : S ⟶ Spec (CommRingCat.of T)) (x y : SchemeHomOver s p'),
      (L.mul s x y).1 ≫ π =
        (G.mul (s ≫ Spec.map (CommRingCat.ofHom f))
          ⟨x.1 ≫ π, by rw [Category.assoc, hP.w, ← Category.assoc, x.2]⟩
          ⟨y.1 ≫ π, by rw [Category.assoc, hP.w, ← Category.assoc, y.2]⟩).1)
    (hone : (L.one (𝟙 (Spec (CommRingCat.of T)))).1 ≫ π =
      Spec.map (CommRingCat.ofHom f) ≫ (G.one (𝟙 (Spec (CommRingCat.of B)))).1)
    (q : ℕ) (P Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of T))) p')
    (hPp : (P.1 ≫ π) ≫ p = Spec.map (CommRingCat.ofHom f))
    (hQp : (Q.1 ≫ π) ≫ p = Spec.map (CommRingCat.ofHom f)) :
    Scheme.IdealSheafData.comap
      (prodKerGraph p
        (fun i : Fin (q * q) ↦ (G.mul (Spec.map (CommRingCat.ofHom f))
          (G.nsmul _ (i.val / q) ⟨P.1 ≫ π, hPp⟩) (G.nsmul _ (i.val % q) ⟨Q.1 ≫ π, hQp⟩)).1)
        (fun i ↦ (G.mul (Spec.map (CommRingCat.ofHom f))
          (G.nsmul _ (i.val / q) ⟨P.1 ≫ π, hPp⟩) (G.nsmul _ (i.val % q) ⟨Q.1 ≫ π, hQp⟩)).2))
      (pullback.lift (pullback.fst p' (𝟙 _) ≫ π) (pullback.snd p' (𝟙 _))
        (by rw [Category.assoc, hP.w, ← Category.assoc, pullback.condition, Category.assoc, Category.id_comp])) =
      prodKerGraph p'
        (fun i : Fin (q * q) ↦ (L.mul (𝟙 _) (L.nsmul _ (i.val / q) P) (L.nsmul _ (i.val % q) Q)).1)
        (fun i ↦ (L.mul (𝟙 _) (L.nsmul _ (i.val / q) P) (L.nsmul _ (i.val % q) Q)).2) := by
  exact main f p p' π hP.w hP G L hmul hone q P Q hPp hQp

end S_WeierstrassProjModel_RelativeGroupLaw_comap_prodKerGraph_linComb_eq_of_isPullback
end P2MW
export P2MW.S_WeierstrassProjModel_RelativeGroupLaw_comap_prodKerGraph_linComb_eq_of_isPullback (solution)
