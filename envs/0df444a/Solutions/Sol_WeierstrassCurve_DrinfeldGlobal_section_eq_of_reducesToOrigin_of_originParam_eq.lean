-- Prove2me | solution 1 for WeierstrassCurve.DrinfeldGlobal.section_eq_of_reducesToOrigin_of_originParam_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/149f54b2-35ad-58d6-9fa7-ab90591eb13f

import Mathlib
import Mathlib
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_DrinfeldGlobal_section_eq_of_reducesToOrigin_of_originParam_eq

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal IsLocalRing

attribute [local instance] MvPolynomial.gradedAlgebra

namespace OSUniqAux

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

lemma apply_sc_eq (P : Section W) (χ : OriginChartRing W →+* T)
    (hχ : IsOriginChartSection P χ) (t : T) :
    χ (fromZeroRingHom (projModelGradingCR W) _ (algebraMap T ((projModelGradingCR W) 0) t)) = t := by
  have h := P.2
  rw [hχ] at h
  simp only [projModelStrCR, Category.assoc, Proj.awayι_toSpecZero_assoc, ← Spec.map_comp] at h
  have h2 : Spec.map (CommRingCat.ofHom (algebraMap T ((projModelGradingCR W) 0)) ≫
      CommRingCat.ofHom (fromZeroRingHom (projModelGradingCR W) _) ≫ CommRingCat.ofHom χ) =
      Spec.map (𝟙 _) := by rw [Spec.map_id]; exact h
  have h3 := Spec.map_injective h2
  have h4 := congrArg (fun g : CommRingCat.of T ⟶ CommRingCat.of T => g.hom t) h3
  simpa using h4

end Model

section Ext
variable {T : Type u} [CommRing T] (W : WeierstrassCurve.Projective T)

theorem originChart_ringHom_ext {S : Type u} [CommRing S] (g₁ g₂ : OriginChartRing W →+* S)
    (hsc : ∀ t : T, g₁ (fromZeroRingHom (projModelGradingCR W) _ (algebraMap T ((projModelGradingCR W) 0) t)) =
      g₂ (fromZeroRingHom (projModelGradingCR W) _ (algebraMap T ((projModelGradingCR W) 0) t)))
    (hx : g₁ (xOverY W) = g₂ (xOverY W)) (hz : g₁ (zOverY W) = g₂ (zOverY W)) : g₁ = g₂ := by
  classical
  have hY : coord W 1 ∈ projModelGradingCR W 1 := coord_mem W 1
  apply RingHom.ext
  intro z
  have hz' : z ∈ Submodule.span ((projModelGradingCR W) 0)
      { (Away.mk (projModelGradingCR W) hY a (∏ i, coord W i ^ ai i)
          (hai ▸ SetLike.prod_pow_mem_graded _ _ _ _ fun i _ ↦ coord_mem W i) : Away (projModelGradingCR W) (coord W 1)) |
        (a : ℕ) (ai : Fin 3 → ℕ) (hai : ∑ i, ai i • (1 : ℕ) = a • 1) } := by
    rw [Away.span_mk_prod_pow_eq_top hY (coord W) (adjoin_range_coord_eq_top W) (fun _ => 1) (fun i => coord_mem W i)]
    trivial
  induction hz' using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨a, ai, hai, rfl⟩ := hz
      have hai' : ai 0 + ai 1 + ai 2 = a := by simpa [Fin.sum_univ_three] using hai
      rw [mk_prod_pow_eq W a ai hai' _ rfl, map_mul, map_pow, map_pow, map_mul, map_pow, map_pow, hx, hz]
  | zero => simp
  | add x y _ _ hx' hy' => rw [map_add, map_add, hx', hy']
  | smul r x _ hx' =>
      obtain ⟨t, ht⟩ := exists_coe_eq_cls_C W r
      have hr : r = algebraMap T ((projModelGradingCR W) 0) t := Subtype.ext (by rw [ht, coe_algebraMap_zero])
      rw [Algebra.smul_def, HomogeneousLocalization.algebraMap_eq, map_mul, map_mul, hx', hr, hsc t]

noncomputable def sc (t : T) : OriginChartRing W :=
  fromZeroRingHom (projModelGradingCR W) _ (algebraMap T ((projModelGradingCR W) 0) t)

theorem originChart_relation :
    zOverY W + sc W W.a₁ * xOverY W * zOverY W + sc W W.a₃ * zOverY W ^ 2 =
      xOverY W ^ 3 + sc W W.a₂ * xOverY W ^ 2 * zOverY W + sc W W.a₄ * xOverY W * zOverY W ^ 2 +
        sc W W.a₆ * zOverY W ^ 3 := by
  have hY : coord W 1 ∈ projModelGradingCR W 1 := coord_mem W 1
  apply val_injective
  have hu : IsUnit (algebraMap (ProjModelRingCR W) (Localization (Submonoid.powers (coord W 1))) (coord W 1)) :=
    IsLocalization.Away.algebraMap_isUnit (coord W 1)
  have hx : algebraMap (ProjModelRingCR W) (Localization (Submonoid.powers (coord W 1))) (coord W 1) * (xOverY W).val =
      algebraMap _ _ (coord W 0) := by
    show _ * (Localization.mk (coord W 0) ⟨coord W 1 ^ 1, ⟨1, rfl⟩⟩ : Localization.Away (coord W 1)) = _
    have h1 : (Localization.mk (coord W 0) ⟨coord W 1 ^ 1, ⟨1, rfl⟩⟩ : Localization.Away (coord W 1)) *
        algebraMap _ _ (coord W 1 ^ 1) = algebraMap _ _ (coord W 0) := by
      rw [Localization.mk_eq_mk']; exact IsLocalization.mk'_spec _ _ _
    rw [map_pow (algebraMap (ProjModelRingCR W) (Localization (Submonoid.powers (coord W 1)))),
      pow_one ((algebraMap (ProjModelRingCR W) (Localization (Submonoid.powers (coord W 1)))) (coord W 1))] at h1
    rw [mul_comm]; exact h1
  have hv : algebraMap (ProjModelRingCR W) (Localization (Submonoid.powers (coord W 1))) (coord W 1) * (zOverY W).val =
      algebraMap _ _ (coord W 2) := by
    show _ * (Localization.mk (coord W 2) ⟨coord W 1 ^ 1, ⟨1, rfl⟩⟩ : Localization.Away (coord W 1)) = _
    have h1 : (Localization.mk (coord W 2) ⟨coord W 1 ^ 1, ⟨1, rfl⟩⟩ : Localization.Away (coord W 1)) *
        algebraMap _ _ (coord W 1 ^ 1) = algebraMap _ _ (coord W 2) := by
      rw [Localization.mk_eq_mk']; exact IsLocalization.mk'_spec _ _ _
    rw [map_pow (algebraMap (ProjModelRingCR W) (Localization (Submonoid.powers (coord W 1)))),
      pow_one ((algebraMap (ProjModelRingCR W) (Localization (Submonoid.powers (coord W 1)))) (coord W 1))] at h1
    rw [mul_comm]; exact h1
  have hsc : ∀ t : T, (sc W t).val =
      algebraMap (ProjModelRingCR W) (Localization (Submonoid.powers (coord W 1)))
        (Ideal.Quotient.mk (projModelHomogeneousIdealCR W).toIdeal (MvPolynomial.C t)) := by
    intro t
    change Localization.mk _ _ = algebraMap _ _ _
    rw [← Localization.mk_one_eq_algebraMap]
    show Localization.mk ((algebraMap T ((projModelGradingCR W) 0) t : (projModelGradingCR W) 0) : ProjModelRingCR W) _ = _
    rw [coe_algebraMap_zero]
    rfl

  have hrel : (algebraMap (ProjModelRingCR W) (Localization (Submonoid.powers (coord W 1))))
      (Ideal.Quotient.mk (projModelHomogeneousIdealCR W).toIdeal W.polynomial) = 0 := by
    have : Ideal.Quotient.mk (projModelHomogeneousIdealCR W).toIdeal W.polynomial = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (by rw [projModelHomogeneousIdealCR_toIdeal]; exact Ideal.subset_span rfl)
    rw [this, map_zero]
  have e : W.polynomial = MvPolynomial.X 1 ^ 2 * MvPolynomial.X 2 + MvPolynomial.C W.a₁ * MvPolynomial.X 0 * MvPolynomial.X 1 * MvPolynomial.X 2
      + MvPolynomial.C W.a₃ * MvPolynomial.X 1 * MvPolynomial.X 2 ^ 2
      - (MvPolynomial.X 0 ^ 3 + MvPolynomial.C W.a₂ * MvPolynomial.X 0 ^ 2 * MvPolynomial.X 2
        + MvPolynomial.C W.a₄ * MvPolynomial.X 0 * MvPolynomial.X 2 ^ 2 + MvPolynomial.C W.a₆ * MvPolynomial.X 2 ^ 3) := rfl
  rw [e] at hrel
  simp only [RingHom.map_sub, RingHom.map_add, RingHom.map_mul, RingHom.map_pow] at hrel
  simp only [val_add, val_mul, val_pow, hsc]
  rw [← hx, ← hv] at hrel
  apply (hu.pow 3).mul_left_cancel
  linear_combination hrel

theorem originChart_v_unique {S : Type u} [CommRing S] [IsLocalRing S] (a₁ a₂ a₃ a₄ a₆ x v v' : S)
    (hx : x ∈ IsLocalRing.maximalIdeal S) (hv : v ∈ IsLocalRing.maximalIdeal S) (hv' : v' ∈ IsLocalRing.maximalIdeal S)
    (h : v + a₁ * x * v + a₃ * v ^ 2 = x ^ 3 + a₂ * x ^ 2 * v + a₄ * x * v ^ 2 + a₆ * v ^ 3)
    (h' : v' + a₁ * x * v' + a₃ * v' ^ 2 = x ^ 3 + a₂ * x ^ 2 * v' + a₄ * x * v' ^ 2 + a₆ * v' ^ 3) :
    v = v' := by
  set B := 1 + a₁ * x + a₃ * (v + v') - a₂ * x ^ 2 - a₄ * x * (v + v') - a₆ * (v ^ 2 + v * v' + v' ^ 2) with hB
  have hprod : (v - v') * B = 0 := by rw [hB]; linear_combination h - h'
  have hBunit : IsUnit B := by
    rw [← IsLocalRing.notMem_maximalIdeal]
    intro hBm
    have h1 : B - 1 ∈ IsLocalRing.maximalIdeal S := by
      rw [hB]
      have := Ideal.add_mem _ (Ideal.add_mem _ (Ideal.mul_mem_left _ a₁ hx)
        (Ideal.mul_mem_left _ a₃ (Ideal.add_mem _ hv hv')))
        (Submodule.neg_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.mul_mem_left _ (a₂ * x) hx)
          (Ideal.mul_mem_left _ (a₄ * x) (Ideal.add_mem _ hv hv')))
          (Ideal.mul_mem_left _ a₆ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.mul_mem_left _ v hv) (Ideal.mul_mem_left _ v hv'))
            (Ideal.mul_mem_left _ v' hv')))))
      convert this using 1; ring
    have : (1 : S) ∈ IsLocalRing.maximalIdeal S := by
      have := Ideal.sub_mem _ hBm h1; simpa using this
    exact (IsLocalRing.maximalIdeal.isMaximal S).ne_top (Ideal.eq_top_of_isUnit_mem _ this isUnit_one)
  exact sub_eq_zero.mp (hBunit.mul_left_eq_zero.mp hprod)

end Ext

end OSUniqAux

open OSUniqAux HomogeneousLocalization in
theorem solution
    {T : Type u} [CommRing T] [IsLocalRing T] [IsAdicComplete (maximalIdeal T) T]
    (W : WeierstrassCurve T) (P P' : Section W) (χ χ' : OriginChartRing W →+* T)
    (hP : ReducesToOrigin P χ (maximalIdeal T)) (hP' : ReducesToOrigin P' χ' (maximalIdeal T))
    (h : originParam χ = originParam χ') :
    P = P' ∧ χ = χ' := by
  obtain ⟨hPχ, hPz, hPw⟩ := hP
  obtain ⟨hPχ', hPz', hPw'⟩ := hP'
  have hx : χ (xOverY W) = χ' (xOverY W) := by
    have := h; simp only [originParam] at this; exact neg_inj.mp this

  have rel := originChart_relation (W : WeierstrassCurve.Projective T)
  have hrelχ := congrArg χ rel
  have hrelχ' := congrArg χ' rel
  simp only [sc, map_add, map_mul, map_pow, apply_sc_eq _ P χ hPχ, apply_sc_eq _ P' χ' hPχ'] at hrelχ hrelχ'
  rw [← hx] at hrelχ'
  have hxm : χ (xOverY W) ∈ IsLocalRing.maximalIdeal T := by
    have := Submodule.neg_mem _ hPz; simpa [originParam] using this
  have hvm : χ (zOverY W) ∈ IsLocalRing.maximalIdeal T := by
    have := Submodule.neg_mem _ hPw; simpa [originW] using this
  have hvm' : χ' (zOverY W) ∈ IsLocalRing.maximalIdeal T := by
    have := Submodule.neg_mem _ hPw'; simpa [originW] using this
  have hv : χ (zOverY W) = χ' (zOverY W) :=
    originChart_v_unique W.a₁ W.a₂ W.a₃ W.a₄ W.a₆ _ _ _ hxm hvm hvm' hrelχ hrelχ'
  have hχ : χ = χ' := originChart_ringHom_ext (W : WeierstrassCurve.Projective T) χ χ'
    (fun t => by rw [apply_sc_eq _ P χ hPχ, apply_sc_eq _ P' χ' hPχ']) hx hv
  refine ⟨Subtype.ext ?_, hχ⟩
  rw [hPχ, hPχ', hχ]

end S_WeierstrassCurve_DrinfeldGlobal_section_eq_of_reducesToOrigin_of_originParam_eq
end P2MW
export P2MW.S_WeierstrassCurve_DrinfeldGlobal_section_eq_of_reducesToOrigin_of_originParam_eq (solution)
