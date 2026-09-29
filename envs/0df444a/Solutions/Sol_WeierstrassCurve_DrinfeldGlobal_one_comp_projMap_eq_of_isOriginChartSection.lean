-- Prove2me | solution 1 for WeierstrassCurve.DrinfeldGlobal.one_comp_projMap_eq_of_isOriginChartSection
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/4018f8f7-33ae-54ef-a1e2-b76588cf3def

import Mathlib
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_WeierstrassCurve_DrinfeldBasisRelative
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_DrinfeldGlobal_one_comp_projMap_eq_of_isOriginChartSection

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal

attribute [local instance] MvPolynomial.gradedAlgebra

namespace K8Aux

open HomogeneousLocalization MvPolynomial HomogeneousIdealQuotientGrading

section AwayCongr

variable {A : Type u} {σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]

def awayCongr {s s' : A} (e : s = s') : Away 𝒜 s ≃+* Away 𝒜 s' := by
  subst e; exact RingEquiv.refl _

lemma awayCongr_mk {s s' : A} (e : s = s') {d : ℕ} (hs : s ∈ 𝒜 d) (hs' : s' ∈ 𝒜 d) (n : ℕ) (x : A)
    (hx : x ∈ 𝒜 (n • d)) :
    awayCongr 𝒜 e (Away.mk 𝒜 hs n x hx) = Away.mk 𝒜 hs' n x hx := by
  subst e; rfl

lemma awayι_eq_specMap_awayCongr_comp {s s' : A} (e : s = s') {i : ℕ} (hs : s ∈ 𝒜 i) (hs' : s' ∈ 𝒜 i)
    (hi : 0 < i) :
    Proj.awayι 𝒜 s' hs' hi =
      Spec.map (CommRingCat.ofHom (awayCongr 𝒜 e).toRingHom) ≫ Proj.awayι 𝒜 s hs hi := by
  subst e
  have : (awayCongr 𝒜 (rfl : s = s)).toRingHom = RingHom.id _ := rfl
  rw [this, CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]

lemma fromZeroRingHom_eq_mk {s : A} {d : ℕ} (hs : s ∈ 𝒜 d) (r : 𝒜 0) :
    fromZeroRingHom 𝒜 (Submonoid.powers s) r = Away.mk 𝒜 hs 0 (r : A) (by simpa using r.2) := by
  apply val_injective
  rw [Away.val_mk]
  show Localization.mk (r : A) _ = Localization.mk (r : A) _
  congr 1
  exact Subtype.ext (pow_zero s).symm

end AwayCongr

section Model

variable {T : Type u} [CommRing T] (W : WeierstrassCurve.Projective T)

lemma coe_algebraMap_zero (t : T) :
    ((algebraMap T ((projModelGradingCR W) 0) t : (projModelGradingCR W) 0) : ProjModelRingCR W) = cls W (C t) := by
  rw [SetLike.GradeZero.coe_algebraMap]; rfl

lemma exists_coe_eq_cls_C (r : (projModelGradingCR W) 0) : ∃ t : T, (r : ProjModelRingCR W) = cls W (C t) := by
  obtain ⟨p, hp, hpr⟩ := (mem_quotGradingSubmodule_iff _ _).mp r.2
  have hp0 : p.IsHomogeneous 0 := (mem_homogeneousSubmodule 0 p).mp hp
  refine ⟨p.coeff 0, ?_⟩
  rw [← hpr]
  by_cases h0 : p = 0
  · subst h0; simp [cls]
  · have htd : p.totalDegree = 0 := hp0.totalDegree h0
    rw [MvPolynomial.totalDegree_eq_zero_iff_eq_C] at htd
    exact congrArg _ htd

lemma adjoin_range_coord_eq_top :
    Algebra.adjoin ((projModelGradingCR W) 0) (Set.range (coord W)) = ⊤ := by
  rw [eq_top_iff]
  rintro x -
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  induction p using MvPolynomial.induction_on with
  | C t =>
      have : (Ideal.Quotient.mk (projModelHomogeneousIdealCR W).toIdeal (C t) : ProjModelRingCR W) =
          algebraMap ((projModelGradingCR W) 0) (ProjModelRingCR W) (algebraMap T ((projModelGradingCR W) 0) t) := by
        rw [SetLike.GradeZero.algebraMap_apply, coe_algebraMap_zero]
      rw [this]
      exact Subalgebra.algebraMap_mem _ _
  | add p q hp hq => rw [map_add]; exact add_mem hp hq
  | mul_X p i hp =>
      rw [map_mul]
      exact mul_mem hp (Algebra.subset_adjoin ⟨i, rfl⟩)

lemma mk_prod_pow_eq (a : ℕ) (ai : Fin 3 → ℕ) (hai : ai 0 + ai 1 + ai 2 = a)
    (x : ProjModelRingCR W) (hxeq : x = ∏ i, coord W i ^ ai i) (hx : x ∈ projModelGradingCR W (a • 1)) :
    Away.mk (projModelGradingCR W) (coord_mem W 1) a x hx = xOverY W ^ ai 0 * zOverY W ^ ai 2 := by
  apply val_injective
  simp only [val_mul, val_pow, xOverY, zOverY, Away.val_mk, Localization.mk_pow, Localization.mk_mul]
  rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [OneMemClass.coe_one, one_mul, Submonoid.coe_mul, SubmonoidClass.coe_pow, hxeq, Fin.prod_univ_three]
  rw [← hai]
  ring

lemma apply_sc_eq {G : RelativeGroupLaw T (projModelStrCR W)} (χ : OriginChartRing W →+* T)
    (hχ : IsOriginChartSection (G.one (𝟙 _)) χ) (t : T) :
    χ (fromZeroRingHom (projModelGradingCR W) _ (algebraMap T ((projModelGradingCR W) 0) t)) = t := by
  have h := (G.one (𝟙 (Spec (CommRingCat.of T)))).2
  rw [hχ] at h
  simp only [projModelStrCR, Category.assoc, Proj.awayι_toSpecZero_assoc, ← Spec.map_comp] at h
  have h2 : Spec.map (CommRingCat.ofHom (algebraMap T ((projModelGradingCR W) 0)) ≫
      CommRingCat.ofHom (fromZeroRingHom (projModelGradingCR W) _) ≫ CommRingCat.ofHom χ) =
      Spec.map (𝟙 _) := by rw [Spec.map_id]; exact h
  have h3 := Spec.map_injective h2
  have h4 := congrArg (fun g : CommRingCat.of T ⟶ CommRingCat.of T => g.hom t) h3
  simpa using h4

end Model

end K8Aux

set_option maxHeartbeats 3200000 in
open K8Aux HomogeneousLocalization in
theorem solution
    {T T' : Type u} [CommRing T] [CommRing T'] (W : WeierstrassCurve.Projective T) (f : T →+* T')
    (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (W.map f))
    (hφ : HomogeneousIdeal.irrelevant (projModelGradingCR (W.map f)) ≤
      (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ)
    (hcoef : IsCoefficientHom W f φ)
    (G : RelativeGroupLaw T (projModelStrCR W)) (L : RelativeGroupLaw T' (projModelStrCR (W.map f)))
    (χ : OriginChartRing W →+* T) (hχ : IsOriginChartSection (G.one (𝟙 _)) χ)
    (hχx : χ (xOverY W) = 0) (hχz : χ (zOverY W) = 0)
    (χ' : OriginChartRing (W.map f) →+* T') (hχ' : IsOriginChartSection (L.one (𝟙 _)) χ')
    (hχ'x : χ' (xOverY (W.map f)) = 0) (hχ'z : χ' (zOverY (W.map f)) = 0) :
    (L.one (𝟙 (Spec (CommRingCat.of T')))).1 ≫ Proj.map φ hφ =
      Spec.map (CommRingCat.ofHom f) ≫ (G.one (𝟙 (Spec (CommRingCat.of T)))).1 := by
  classical

  have hY : coord W 1 ∈ projModelGradingCR W 1 := coord_mem W 1
  have hY' : coord (W.map f) 1 ∈ projModelGradingCR (W.map f) 1 := coord_mem (W.map f) 1
  have e : φ (coord W 1) = coord (W.map f) 1 := hcoef.2 1
  have hφY : φ (coord W 1) ∈ projModelGradingCR (W.map f) 1 := φ.2 hY

  rw [hχ', hχ]
  show Spec.map (CommRingCat.ofHom χ') ≫ Proj.awayι (projModelGradingCR (W.map f)) (coord (W.map f) 1) hY' one_pos ≫
      Proj.map φ hφ =
    Spec.map (CommRingCat.ofHom f) ≫ Spec.map (CommRingCat.ofHom χ) ≫
      Proj.awayι (projModelGradingCR W) (coord W 1) hY one_pos
  rw [awayι_eq_specMap_awayCongr_comp (projModelGradingCR (W.map f)) e hφY hY' one_pos, Category.assoc,
    Proj.awayι_comp_map φ hφ one_pos (coord W 1) hY, ← Spec.map_comp_assoc, ← Spec.map_comp_assoc, ← Spec.map_comp_assoc]

  suffices key : (χ'.comp (awayCongr (projModelGradingCR (W.map f)) e).toRingHom).comp
      (Away.map φ (coord W 1)) = f.comp χ by
    have : CommRingCat.ofHom (Away.map φ (coord W 1)) ≫
        CommRingCat.ofHom (awayCongr (projModelGradingCR (W.map f)) e).toRingHom ≫ CommRingCat.ofHom χ' =
        CommRingCat.ofHom χ ≫ CommRingCat.ofHom f := by
      rw [← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
      exact congrArg CommRingCat.ofHom key
    rw [this]

  apply RingHom.ext
  intro z
  have hz : z ∈ Submodule.span ((projModelGradingCR W) 0)
      { (Away.mk (projModelGradingCR W) hY a (∏ i, coord W i ^ ai i)
          (hai ▸ SetLike.prod_pow_mem_graded _ _ _ _ fun i _ ↦ coord_mem W i) : Away (projModelGradingCR W) (coord W 1)) |
        (a : ℕ) (ai : Fin 3 → ℕ) (hai : ∑ i, ai i • (1 : ℕ) = a • 1) } := by
    rw [Away.span_mk_prod_pow_eq_top hY (coord W) (adjoin_range_coord_eq_top W) (fun _ => 1) (fun i => coord_mem W i)]
    trivial
  induction hz using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨a, ai, hai, rfl⟩ := hz
      have hai' : ai 0 + ai 1 + ai 2 = a := by simpa [Fin.sum_univ_three] using hai

      have hprod : φ (∏ i, coord W i ^ ai i) = ∏ i, coord (W.map f) i ^ ai i := by
        rw [map_prod]
        exact Finset.prod_congr rfl fun i _ => by rw [map_pow, hcoef.2 i]
      simp only [RingHom.coe_comp, Function.comp_apply, Away.map_mk, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
      rw [awayCongr_mk (projModelGradingCR (W.map f)) e hφY hY',
        mk_prod_pow_eq (W.map f) a ai hai' _ hprod, mk_prod_pow_eq W a ai hai' _ rfl,
        map_mul, map_pow, map_pow, hχ'x, hχ'z, map_mul, map_pow, map_pow, hχx, hχz, map_mul, map_pow, map_pow, map_zero]
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, map_add, hx, hy]
  | smul r x _ hx =>
      obtain ⟨t, ht⟩ := exists_coe_eq_cls_C W r
      have hr : r = algebraMap T ((projModelGradingCR W) 0) t := Subtype.ext (by rw [ht, coe_algebraMap_zero])
      rw [Algebra.smul_def, algebraMap_eq, map_mul, map_mul, hx]
      congr 1
      subst hr

      simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
      rw [apply_sc_eq W χ hχ t]
      rw [fromZeroRingHom_eq_mk (projModelGradingCR W) hY]
      rw [Away.map_mk]
      rw [awayCongr_mk (projModelGradingCR (W.map f)) e hφY hY' 0]
      have hφt : φ ((algebraMap T ((projModelGradingCR W) 0) t : (projModelGradingCR W) 0) : ProjModelRingCR W) =
          ((algebraMap T' ((projModelGradingCR (W.map f)) 0) (f t) : (projModelGradingCR (W.map f)) 0) :
            ProjModelRingCR (W.map f)) := by
        rw [coe_algebraMap_zero, coe_algebraMap_zero, hcoef.1 t]
      have hsc := apply_sc_eq (W.map f) χ' hχ' (f t)
      rw [fromZeroRingHom_eq_mk (projModelGradingCR (W.map f)) hY'] at hsc
      have hmk : ∀ (x₁ x₂ : ProjModelRingCR (W.map f)) (h₁ : x₁ ∈ projModelGradingCR (W.map f) (0 • 1))
          (h₂ : x₂ ∈ projModelGradingCR (W.map f) (0 • 1)), x₁ = x₂ →
          Away.mk (projModelGradingCR (W.map f)) hY' 0 x₁ h₁ = Away.mk (projModelGradingCR (W.map f)) hY' 0 x₂ h₂ := by
        intro x₁ x₂ h₁ h₂ h; subst h; rfl
      rw [hmk _ _ _ _ hφt]
      exact hsc

end S_WeierstrassCurve_DrinfeldGlobal_one_comp_projMap_eq_of_isOriginChartSection
end P2MW
export P2MW.S_WeierstrassCurve_DrinfeldGlobal_one_comp_projMap_eq_of_isOriginChartSection (solution)
