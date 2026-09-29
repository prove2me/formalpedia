-- Prove2me | solution 1 for WeierstrassCurve.DrinfeldGlobal.ker_eq_span_of_originChartRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/5e80d384-f164-5b34-95b6-91b7010db3f7

import Mathlib
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_DrinfeldGlobal_ker_eq_span_of_originChartRing

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal IsLocalRing HomogeneousLocalization

attribute [local instance] MvPolynomial.gradedAlgebra

namespace ChartGenAux
open HomogeneousLocalization MvPolynomial HomogeneousIdealQuotientGrading

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

end Model
end ChartGenAux

open ChartGenAux HomogeneousLocalization in
theorem solution
    {T : Type u} [CommRing T] (W : WeierstrassCurve T) (χ : OriginChartRing W →+* T)
    (hsc : ∀ t : T, χ (fromZeroRingHom (projModelGradingCR W) _ (algebraMap T ((projModelGradingCR W) 0) t)) = t) :
    RingHom.ker χ = Ideal.span
      {xOverY W - fromZeroRingHom (projModelGradingCR W) _ (algebraMap T ((projModelGradingCR W) 0) (χ (xOverY W))),
       zOverY W - fromZeroRingHom (projModelGradingCR W) _ (algebraMap T ((projModelGradingCR W) 0) (χ (zOverY W)))} := by
  classical
  have hY : coord W 1 ∈ projModelGradingCR W 1 := coord_mem W 1

  set sc : T →+* OriginChartRing W :=
    (fromZeroRingHom (projModelGradingCR W) _).comp (algebraMap T ((projModelGradingCR W) 0)) with hscdef
  have hsc' : ∀ t, χ (sc t) = t := fun t => by rw [hscdef]; exact hsc t
  set I : Ideal (OriginChartRing W) := Ideal.span {xOverY W - sc (χ (xOverY W)), zOverY W - sc (χ (zOverY W))} with hI
  change RingHom.ker χ = I
  apply le_antisymm
  ·
    have key : ∀ z : OriginChartRing W, z - sc (χ z) ∈ I := by
      have pmul : ∀ z₁ z₂ : OriginChartRing W, z₁ - sc (χ z₁) ∈ I → z₂ - sc (χ z₂) ∈ I →
          z₁ * z₂ - sc (χ (z₁ * z₂)) ∈ I := by
        intro z₁ z₂ h₁ h₂
        have : z₁ * z₂ - sc (χ (z₁ * z₂)) = z₁ * (z₂ - sc (χ z₂)) + sc (χ z₂) * (z₁ - sc (χ z₁)) := by
          rw [map_mul, map_mul]; ring
        rw [this]
        exact I.add_mem (I.mul_mem_left _ h₂) (I.mul_mem_left _ h₁)
      have ppow : ∀ (z : OriginChartRing W) (n : ℕ), z - sc (χ z) ∈ I → z ^ n - sc (χ (z ^ n)) ∈ I := by
        intro z n h
        induction n with
        | zero => simp [map_one]
        | succ n ih => rw [pow_succ]; exact pmul _ _ ih h
      have px : xOverY W - sc (χ (xOverY W)) ∈ I := Ideal.subset_span (by simp)
      have pz : zOverY W - sc (χ (zOverY W)) ∈ I := Ideal.subset_span (by simp)
      intro z
      have hzs : z ∈ Submodule.span ((projModelGradingCR W) 0)
          { (Away.mk (projModelGradingCR W) hY a (∏ i, coord W i ^ ai i)
              (hai ▸ SetLike.prod_pow_mem_graded _ _ _ _ fun i _ ↦ coord_mem W i) : Away (projModelGradingCR W) (coord W 1)) |
            (a : ℕ) (ai : Fin 3 → ℕ) (hai : ∑ i, ai i • (1 : ℕ) = a • 1) } := by
        rw [Away.span_mk_prod_pow_eq_top hY (coord W) (adjoin_range_coord_eq_top W) (fun _ => 1) (fun i => coord_mem W i)]
        trivial
      induction hzs using Submodule.span_induction with
      | mem z hz =>
          obtain ⟨a, ai, hai, rfl⟩ := hz
          have hai' : ai 0 + ai 1 + ai 2 = a := by simpa [Fin.sum_univ_three] using hai
          rw [mk_prod_pow_eq W a ai hai' _ rfl]
          exact pmul _ _ (ppow _ _ px) (ppow _ _ pz)
      | zero => simp
      | add x y _ _ hx' hy' =>
          have : x + y - sc (χ (x + y)) = (x - sc (χ x)) + (y - sc (χ y)) := by rw [map_add, map_add]; ring
          rw [this]; exact I.add_mem hx' hy'
      | smul r x _ hx' =>
          obtain ⟨t, ht⟩ := exists_coe_eq_cls_C W r
          have hr : r = algebraMap T ((projModelGradingCR W) 0) t := Subtype.ext (by rw [ht, coe_algebraMap_zero])
          subst hr
          rw [Algebra.smul_def, algebraMap_eq]
          have e1 : fromZeroRingHom (projModelGradingCR W) _ (algebraMap T ((projModelGradingCR W) 0) t) = sc t := by
            rw [hscdef]; rfl
          rw [e1, map_mul, hsc', map_mul, ← mul_sub]
          exact I.mul_mem_left _ hx'
    intro z hz
    have h := key z
    rw [RingHom.mem_ker] at hz
    rwa [hz, map_zero, sub_zero] at h
  · rw [hI, Ideal.span_le]
    rintro w hw
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with rfl | rfl
    · rw [SetLike.mem_coe, RingHom.mem_ker, map_sub, hsc', sub_self]
    · rw [SetLike.mem_coe, RingHom.mem_ker, map_sub, hsc', sub_self]

end S_WeierstrassCurve_DrinfeldGlobal_ker_eq_span_of_originChartRing
end P2MW
export P2MW.S_WeierstrassCurve_DrinfeldGlobal_ker_eq_span_of_originChartRing (solution)
