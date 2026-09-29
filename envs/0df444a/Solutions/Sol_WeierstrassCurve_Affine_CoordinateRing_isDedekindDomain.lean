-- Prove2me | solution 1 for WeierstrassCurve.Affine.CoordinateRing.isDedekindDomain
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/64a9d5c5-cba3-540c-9046-bf7ed3b09d5e

import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Tactic.LinearCombination
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_Affine_CoordinateRing_isDedekindDomain

p2m_open "Polynomial WeierstrassCurve P2MW.S_WeierstrassCurve_Affine_CoordinateRing_isDedekindDomain.WeierstrassCurve WeierstrassCurve.Affine P2MW.S_WeierstrassCurve_Affine_CoordinateRing_isDedekindDomain.WeierstrassCurve.Affine WeierstrassCurve.Affine.CoordinateRing P2MW.S_WeierstrassCurve_Affine_CoordinateRing_isDedekindDomain.WeierstrassCurve.Affine.CoordinateRing"
open scoped Polynomial.Bivariate

local macro "C_simp" : tactic =>
  `(tactic| simp only [map_ofNat, C_0, C_1, C_neg, C_add, C_sub, C_mul, C_pow])

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine a₃ a₁ map Affine.CoordinateRing mk a₄ a₂ toAffine Affine.Point Δ"
namespace Affine
p2m_export "WeierstrassCurve.Affine" "Equation negY CoordinateRing map evalEval_polynomialX Nonsingular Point evalEval_polynomialY equation_iff_nonsingular CoordinateRing.basis equation_iff polynomial"
namespace CoordinateRing
p2m_export "WeierstrassCurve.Affine.CoordinateRing" "XYIdeal quotientXYIdealEquiv XClass_ne_zero YClass mk map XClass"
namespace DetInfra
p2m_open "WeierstrassCurve.Affine.CoordinateRing WeierstrassCurve.Affine WeierstrassCurve"

open IsLocalRing

variable {F : Type*} [Field F] {W : Affine F}

lemma XYIdeal_eq_map (x : F) (y : F[X]) :
    XYIdeal W x y = Ideal.map (mk W) (Ideal.span {C (X - C x), Y - C y}) := by
  simp only [XYIdeal, XClass, YClass, ← Set.image_pair, ← Ideal.map_span]

lemma mk_mem_XYIdeal_of_evalEval_eq_zero (x y : F) {p : F[X][Y]} (hp : p.evalEval x y = 0) :
    mk W p ∈ XYIdeal W x (C y) := by
  rw [XYIdeal_eq_map]
  exact Ideal.mem_map_of_mem _ (mem_span_C_X_sub_C_X_sub_C_iff_eval_eval_eq_zero.mpr hp)

lemma mk_mem_XYIdeal_iff' {x y : F} (h : W.Equation x y) (p : F[X][Y]) :
    mk W p ∈ XYIdeal W x (C y) ↔ p.evalEval x y = 0 := by
  refine ⟨fun hp => ?_, mk_mem_XYIdeal_of_evalEval_eq_zero x y⟩
  rw [XYIdeal_eq_map, Ideal.mem_map_iff_of_surjective _ AdjoinRoot.mk_surjective] at hp
  obtain ⟨q, hq, hqp⟩ := hp
  obtain ⟨r, hr⟩ := AdjoinRoot.mk_eq_mk.mp hqp
  have hW : W.polynomial ∈ Ideal.span {C (X - C x), Y - C (C y)} :=
    mem_span_C_X_sub_C_X_sub_C_iff_eval_eval_eq_zero.mpr h
  have : p = q - W.polynomial * r := by rw [← hr]; ring
  rw [this]
  exact mem_span_C_X_sub_C_X_sub_C_iff_eval_eval_eq_zero.mp
    (Ideal.sub_mem _ hq (Ideal.mul_mem_right _ _ hW))

lemma isMaximal_XYIdeal' {x y : F} (h : W.Equation x y) : (XYIdeal W x (C y)).IsMaximal :=
  Ideal.Quotient.maximal_of_isField _ <|
    MulEquiv.isField (Field.toIsField F) (quotientXYIdealEquiv (W' := W) h).toMulEquiv

lemma XYIdeal_ne_bot (x : F) (y : F[X]) : XYIdeal W x y ≠ ⊥ := fun h0 =>
  XClass_ne_zero (W' := W) x <| by
    have : XClass W x ∈ XYIdeal W x y := Ideal.subset_span (by simp)
    rwa [h0, Ideal.mem_bot] at this

theorem isMaximal_iff_exists_eq_XYIdeal' [IsAlgClosed F] (I : Ideal W.CoordinateRing) :
    I.IsMaximal ↔ ∃ x y : F, W.Equation x y ∧ I = XYIdeal W x (C y) := by
  constructor
  · intro hI
    letI := Ideal.Quotient.field I
    have : Module.Finite F (W.CoordinateRing ⧸ I) :=
      finite_of_finite_type_of_isJacobsonRing F _
    have hbij := IsAlgClosed.algebraMap_bijective_of_isIntegral (k := F)
      (K := W.CoordinateRing ⧸ I)
    obtain ⟨x, hx⟩ := hbij.2 (Ideal.Quotient.mk I (mk W (C X)))
    obtain ⟨y, hy⟩ := hbij.2 (Ideal.Quotient.mk I (mk W Y))
    have hxI : XClass W x ∈ I := by
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      simp only [XClass, map_sub, ← hx, sub_eq_zero]
      rfl
    have hyI : YClass W (C y) ∈ I := by
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      simp only [YClass, map_sub, ← hy, sub_eq_zero]
      rfl
    have hle : XYIdeal W x (C y) ≤ I :=
      Ideal.span_le.mpr (Set.insert_subset_iff.mpr ⟨hxI, Set.singleton_subset_iff.mpr hyI⟩)
    have heq : W.Equation x y := by
      by_contra hne
      refine hI.ne_top (I.eq_top_of_isUnit_mem (hle <| mk_mem_XYIdeal_of_evalEval_eq_zero x y
        (p := W.polynomial - C (C (W.polynomial.evalEval x y))) ?_) ?_)
      · simp only [evalEval_sub, evalEval_CC, sub_self]
      · rw [map_sub, AdjoinRoot.mk_self, zero_sub, IsUnit.neg_iff]
        exact (Ne.isUnit hne).map (algebraMap F W.CoordinateRing)
    exact ⟨x, y, heq, ((isMaximal_XYIdeal' heq).eq_of_le hI.ne_top hle).symm⟩
  · rintro ⟨x, y, h, rfl⟩
    exact isMaximal_XYIdeal' h

lemma span_pair_eq_span_singleton_of_mul_eq {R : Type*} [CommRing R] {a b c u : R}
    (hu : IsUnit u) (h : b * u = a * c) : Ideal.span {a, b} = Ideal.span {a} := by
  refine le_antisymm (Ideal.span_le.mpr <| Set.insert_subset_iff.mpr
    ⟨Ideal.mem_span_singleton_self a, Set.singleton_subset_iff.mpr ?_⟩)
    (Ideal.span_mono <| Set.singleton_subset_iff.mpr <| Set.mem_insert _ _)
  obtain ⟨u, rfl⟩ := hu
  exact Ideal.mem_span_singleton'.mpr ⟨c * ↑u⁻¹, by
    rw [show c * ↑u⁻¹ * a = a * c * ↑u⁻¹ by ring, ← h, Units.mul_inv_cancel_right]⟩

lemma map_XYIdeal {S : Type*} [CommRing S] (f : W.CoordinateRing →+* S) (x : F) (y : F[X]) :
    (XYIdeal W x y).map f = Ideal.span {f (XClass W x), f (YClass W y)} := by
  rw [XYIdeal, Ideal.map_span, Set.image_pair]

theorem isPrincipal_maximalIdeal_localization {x y : F} (h : W.Nonsingular x y)
    [(XYIdeal W x (C y)).IsPrime] :
    (maximalIdeal (Localization.AtPrime (XYIdeal W x (C y)))).IsPrincipal := by
  set L := Localization.AtPrime (XYIdeal W x (C y))
  have hI : maximalIdeal L =
      Ideal.span {algebraMap _ L (XClass W x), algebraMap _ L (YClass W (C y))} := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal, map_XYIdeal]

  set g : F[X][Y] := C (X ^ 2 + C (x + W.a₂) * X + C (x ^ 2 + W.a₂ * x + W.a₄)) - C (C W.a₁) * Y
    with hg
  have key : YClass W (C y) * YClass W (C (W.negY x y)) = XClass W x * mk W g := by
    simp only [YClass, XClass, ← map_mul]
    exact AdjoinRoot.mk_eq_mk.mpr ⟨1, by
      linear_combination (norm := (rw [hg, negY, polynomial]; C_simp; ring1))
        congr_arg C (congr_arg C ((equation_iff ..).mp h.left).symm)⟩
  have key' : algebraMap _ L (YClass W (C y)) * algebraMap _ L (YClass W (C (W.negY x y))) =
      algebraMap _ L (XClass W x) * algebraMap _ L (mk W g) := by
    rw [← map_mul, ← map_mul, key]
  have hmem : ∀ p : F[X][Y], mk W p ∈ XYIdeal W x (C y) ↔ p.evalEval x y = 0 :=
    mk_mem_XYIdeal_iff' h.left
  rcases h.right with hx | hy
  ·
    have hgu : IsUnit (algebraMap _ L (mk W g)) := by
      rw [IsLocalization.AtPrime.isUnit_to_map_iff L (XYIdeal W x (C y))]
      intro (hgI : mk W g ∈ XYIdeal W x (C y))
      apply hx
      have h0 := (hmem g).mp hgI
      rw [evalEval_polynomialX]
      simp only [hg, evalEval_sub, evalEval_mul, evalEval_C, evalEval_X, eval_add, eval_mul,
        eval_pow, eval_C, eval_X] at h0
      linear_combination -h0
    refine ⟨⟨algebraMap _ L (YClass W (C y)), ?_⟩⟩
    rw [hI, Ideal.span_insert, sup_comm, ← Ideal.span_insert]
    exact span_pair_eq_span_singleton_of_mul_eq hgu key'.symm
  ·
    have hyu : IsUnit (algebraMap _ L (YClass W (C (W.negY x y)))) := by
      rw [IsLocalization.AtPrime.isUnit_to_map_iff L (XYIdeal W x (C y))]
      intro (hyI : mk W (Y - C (C (W.negY x y))) ∈ XYIdeal W x (C y))
      apply hy
      have h0 := (hmem _).mp hyI
      rw [evalEval_polynomialY]
      simp only [evalEval_sub, evalEval_CC, evalEval_X, negY] at h0
      linear_combination h0
    refine ⟨⟨algebraMap _ L (XClass W x), ?_⟩⟩
    rw [hI]
    exact span_pair_eq_span_singleton_of_mul_eq hyu key'

theorem isDiscreteValuationRing_localization_XYIdeal' {x y : F} (h : W.Nonsingular x y)
    [(XYIdeal W x (C y)).IsPrime] :
    IsDiscreteValuationRing (Localization.AtPrime (XYIdeal W x (C y))) := by
  have hnf := IsLocalization.AtPrime.not_isField W.CoordinateRing (XYIdeal_ne_bot x (C y))
    (Localization.AtPrime (XYIdeal W x (C y)))
  haveI : IsNoetherianRing (Localization.AtPrime (XYIdeal W x (C y))) :=
    IsLocalization.isNoetherianRing (XYIdeal W x (C y)).primeCompl _ inferInstance
  exact ((IsDiscreteValuationRing.TFAE _ hnf).out 0 4).mpr
    (isPrincipal_maximalIdeal_localization h)

scoped instance : Module.Finite F[X] W.CoordinateRing := Module.Finite.of_basis (CoordinateRing.basis W)

lemma isMaximal_of_isPrime_of_ne_bot (P : Ideal W.CoordinateRing) [P.IsPrime] (hP : P ≠ ⊥) :
    P.IsMaximal :=
  Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := F[X]) P <|
    IsPrime.to_maximal_ideal (Ideal.under_ne_bot F[X] hP)

theorem isDedekindDomain_of_isAlgClosed' [IsAlgClosed F] [W.IsElliptic] :
    IsDedekindDomain W.CoordinateRing := by
  have : IsDedekindDomainDvr W.CoordinateRing := by
    refine ⟨fun P hP hPp => ?_⟩
    have hmax : P.IsMaximal := isMaximal_of_isPrime_of_ne_bot P hP
    obtain ⟨x, y, hxy, rfl⟩ := (isMaximal_iff_exists_eq_XYIdeal' P).mp hmax
    exact isDiscreteValuationRing_localization_XYIdeal' (equation_iff_nonsingular.mp hxy)
  infer_instance

end WeierstrassCurve.Affine.CoordinateRing.DetInfra
p2m_reactivate "P2MW.S_WeierstrassCurve_Affine_CoordinateRing_isDedekindDomain.WeierstrassCurve P2MW.S_WeierstrassCurve_Affine_CoordinateRing_isDedekindDomain.WeierstrassCurve.Affine P2MW.S_WeierstrassCurve_Affine_CoordinateRing_isDedekindDomain.WeierstrassCurve.Affine.CoordinateRing P2MW.S_WeierstrassCurve_Affine_CoordinateRing_isDedekindDomain.WeierstrassCurve.Affine.CoordinateRing.DetInfra"
p2m_reactivate "P2MW.S_WeierstrassCurve_Affine_CoordinateRing_isDedekindDomain.WeierstrassCurve P2MW.S_WeierstrassCurve_Affine_CoordinateRing_isDedekindDomain.WeierstrassCurve.Affine P2MW.S_WeierstrassCurve_Affine_CoordinateRing_isDedekindDomain.WeierstrassCurve.Affine.CoordinateRing"
p2m_reactivate "P2MW.S_WeierstrassCurve_Affine_CoordinateRing_isDedekindDomain.WeierstrassCurve P2MW.S_WeierstrassCurve_Affine_CoordinateRing_isDedekindDomain.WeierstrassCurve.Affine"
p2m_reactivate "P2MW.S_WeierstrassCurve_Affine_CoordinateRing_isDedekindDomain.WeierstrassCurve"

open WeierstrassCurve.Affine.CoordinateRing.DetInfra

theorem solution {K : Type*} [Field K] [IsAlgClosed K] (W : WeierstrassCurve K) [W.IsElliptic] : IsDedekindDomain W.toAffine.CoordinateRing :=
  isDedekindDomain_of_isAlgClosed' (W := W.toAffine)

end S_WeierstrassCurve_Affine_CoordinateRing_isDedekindDomain
end P2MW
export P2MW.S_WeierstrassCurve_Affine_CoordinateRing_isDedekindDomain (solution)
