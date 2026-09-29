-- Prove2me | solution 1 for WeierstrassCurve.Affine.CoordinateRing.natDegree_norm_eq_finsum_count
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/8e86cef3-7601-59a5-8e6a-6f0e0d7fd352

import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.FreeModule.Norm
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_Affine_CoordinateRing_natDegree_norm_eq_finsum_count

p2m_open "IsDedekindDomain P2MW.S_WeierstrassCurve_Affine_CoordinateRing_natDegree_norm_eq_finsum_count.IsDedekindDomain Module"

namespace IsDedekindDomain
p2m_export "IsDedekindDomain" "HeightOneSpectrum.quotientEquivPiOfProdEq quotientEquivPiOfProdEq mk HeightOneSpectrum"
p2m_open "IsDedekindDomain"

variable (K : Type*) {R : Type*} [Field K] [CommRing R] [IsDedekindDomain R] [Algebra K R]

section Filtration

variable {P : Ideal R} [P.IsPrime]

theorem finrank_quotient_pow_succ (hP : P ≠ ⊥) (c : ℕ) [Module.Finite K (R ⧸ P ^ (c + 1))] :
    finrank K (R ⧸ P ^ (c + 1)) = finrank K (R ⧸ P ^ c) + finrank K (R ⧸ P) := by
  obtain ⟨a, ha, ha'⟩ := SetLike.exists_of_lt (Ideal.pow_succ_lt_pow hP c)

  let π : (R ⧸ P ^ (c + 1)) →ₐ[K] R ⧸ P ^ c :=
    Ideal.Quotient.factorₐ K (Ideal.pow_le_pow_right c.le_succ)
  have hπ : Function.Surjective π := fun x => by
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact ⟨Ideal.Quotient.mk _ y, rfl⟩

  let m : (R ⧸ P) →ₗ[R] R ⧸ P ^ (c + 1) :=
    Submodule.liftQ P ((Submodule.mkQ (P ^ (c + 1))) ∘ₗ LinearMap.mulLeft R a) (by
      intro x hx
      rw [LinearMap.mem_ker, LinearMap.comp_apply, LinearMap.mulLeft_apply, Submodule.mkQ_apply,
        Submodule.Quotient.mk_eq_zero, pow_succ]
      exact Ideal.mul_mem_mul ha hx)
  have hm_mk : ∀ x : R, m (Ideal.Quotient.mk P x) = Ideal.Quotient.mk (P ^ (c + 1)) (a * x) :=
    fun _ => rfl
  have hm : Function.Injective (m.restrictScalars K) := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro x hx
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [LinearMap.mem_ker, LinearMap.restrictScalars_apply, hm_mk,
      Ideal.Quotient.eq_zero_iff_mem] at hx
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_prime_of_mul_mem_pow hP ha' hx)
  have hrange : LinearMap.range (m.restrictScalars K) = LinearMap.ker π.toLinearMap := by
    ext x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [LinearMap.mem_ker, AlgHom.toLinearMap_apply, Ideal.Quotient.factorₐ_apply_mk,
      Ideal.Quotient.eq_zero_iff_mem, LinearMap.mem_range]
    constructor
    · rintro ⟨y, hy⟩
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
      rw [LinearMap.restrictScalars_apply, hm_mk, Ideal.Quotient.eq] at hy
      have := sub_mem (Ideal.mul_mem_right y _ ha) (Ideal.pow_le_pow_right c.le_succ hy)
      rwa [sub_sub_cancel] at this
    · intro hx
      obtain ⟨d, e, he, hde⟩ := Ideal.exists_mul_add_mem_pow_succ hP a x ha ha' hx
      refine ⟨Ideal.Quotient.mk P d, ?_⟩
      rw [LinearMap.restrictScalars_apply, hm_mk, Ideal.Quotient.eq, ← hde]
      simpa using he
  rw [← (LinearMap.finrank_range_add_finrank_ker π.toLinearMap), LinearMap.range_eq_top.mpr hπ,
    finrank_top, ← hrange, LinearMap.finrank_range_of_inj hm]

theorem finrank_quotient_pow (hP : P ≠ ⊥) :
    ∀ (c : ℕ) [Module.Finite K (R ⧸ P ^ c)], finrank K (R ⧸ P ^ c) = c * finrank K (R ⧸ P)
  | 0, _ => by
    haveI : Subsingleton (R ⧸ P ^ 0) :=
      Ideal.Quotient.subsingleton_iff.mpr ((pow_zero P).trans Ideal.one_eq_top)
    rw [zero_mul, finrank_zero_of_subsingleton]
  | c + 1, _ => by
    haveI : Module.Finite K (R ⧸ P ^ c) := Module.Finite.of_surjective
      (Ideal.Quotient.factorₐ K (Ideal.pow_le_pow_right c.le_succ) :
        (R ⧸ P ^ (c + 1)) →ₐ[K] R ⧸ P ^ c).toLinearMap
      (fun x => by
        obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
        exact ⟨Ideal.Quotient.mk _ y, rfl⟩)
    rw [finrank_quotient_pow_succ K hP c, finrank_quotient_pow hP c, add_mul, one_mul]

end Filtration

open scoped Classical in

theorem finrank_quotient_eq_finsum {I : Ideal R} (hI : I ≠ ⊥) [Module.Finite K (R ⧸ I)] :
    finrank K (R ⧸ I) = ∑ᶠ v : HeightOneSpectrum R,
      (Associates.mk v.asIdeal).count (Associates.mk I).factors * finrank K (R ⧸ v.asIdeal) := by
  set c : HeightOneSpectrum R → ℕ := fun v => (Associates.mk v.asIdeal).count (Associates.mk I).factors
    with hc
  set T := (Ideal.finite_factors hI).toFinset with hT
  have hcT : ∀ v, c v ≠ 0 → v ∈ T := fun v hv =>
    (Ideal.finite_factors hI).mem_toFinset.mpr ((Associates.count_ne_zero_iff_dvd hI v.irreducible).mp hv)

  have hprod : ∏ v : T, (v : HeightOneSpectrum R).asIdeal ^ c v = I := by
    rw [Finset.prod_coe_sort T fun v => v.asIdeal ^ c v, ← Ideal.finprod_heightOneSpectrum_factorization hI]
    refine (finprod_eq_prod_of_mulSupport_subset _ fun v hv => ?_).symm
    refine hcT v fun h0 => hv ?_
    simp only [h0, pow_zero]

  let e : (R ⧸ I) ≃ₐ[K] ∀ v : T, R ⧸ (v : HeightOneSpectrum R).asIdeal ^ c v :=
    AlgEquiv.ofRingEquiv (f := HeightOneSpectrum.quotientEquivPiOfProdEq I (fun v : T => v.1) (fun v => c v)
      (fun _ _ h => Subtype.coe_injective.ne h) hprod) (fun _ => rfl)
  haveI : Module.Finite K (∀ v : T, R ⧸ (v : HeightOneSpectrum R).asIdeal ^ c v) :=
    Module.Finite.equiv e.toLinearEquiv
  have hφ : ∀ v : T, Function.Surjective
      (LinearMap.proj (R := K) (φ := fun w : T => R ⧸ (w : HeightOneSpectrum R).asIdeal ^ c w) v) :=
    fun v => LinearMap.proj_surjective v
  haveI : ∀ v : T, Module.Finite K (R ⧸ (v : HeightOneSpectrum R).asIdeal ^ c v) := fun v =>
    Module.Finite.of_surjective _ (hφ v)
  rw [e.toLinearEquiv.finrank_eq,
    finsum_eq_sum_of_support_subset _ (s := T) fun v hv =>
      hcT v (left_ne_zero_of_mul (Function.mem_support.mp hv))]
  calc finrank K (∀ v : T, R ⧸ (v : HeightOneSpectrum R).asIdeal ^ c v)
      = ∑ v : T, finrank K (R ⧸ (v : HeightOneSpectrum R).asIdeal ^ c v) :=
        Module.finrank_pi_fintype K
    _ = ∑ v : T, c v * finrank K (R ⧸ (v : HeightOneSpectrum R).asIdeal) :=
        Finset.sum_congr rfl fun v _ => finrank_quotient_pow K v.1.ne_bot (c v)
    _ = ∑ v ∈ T, c v * finrank K (R ⧸ v.asIdeal) :=
        Finset.sum_coe_sort T fun v => c v * finrank K (R ⧸ v.asIdeal)

open scoped Classical in

theorem finrank_quotient_eq_finsum_of_isAlgClosed [IsAlgClosed K] {I : Ideal R} (hI : I ≠ ⊥)
    [Module.Finite K (R ⧸ I)] :
    finrank K (R ⧸ I) =
      ∑ᶠ v : HeightOneSpectrum R, (Associates.mk v.asIdeal).count (Associates.mk I).factors := by
  rw [finrank_quotient_eq_finsum K hI]
  refine finsum_congr fun v => ?_
  by_cases hv : (Associates.mk v.asIdeal).count (Associates.mk I).factors = 0
  · rw [hv, zero_mul]
  · have hle : I ≤ v.asIdeal :=
      Ideal.le_of_dvd ((Associates.count_ne_zero_iff_dvd hI v.irreducible).mp hv)
    haveI : Module.Finite K (R ⧸ v.asIdeal) := Module.Finite.of_surjective
      (Ideal.Quotient.factorₐ K hle : (R ⧸ I) →ₐ[K] R ⧸ v.asIdeal).toLinearMap
      (fun x => by
        obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
        exact ⟨Ideal.Quotient.mk _ y, rfl⟩)
    haveI : Algebra.IsIntegral K (R ⧸ v.asIdeal) := Algebra.IsIntegral.of_finite K _
    rw [← (LinearEquiv.ofBijective (Algebra.linearMap K (R ⧸ v.asIdeal))
      (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := K))).finrank_eq, Module.finrank_self,
      mul_one]

end IsDedekindDomain

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine Affine.CoordinateRing mk IsIntegral toAffine Affine.Point"
namespace Affine
p2m_export "WeierstrassCurve.Affine" "CoordinateRing FunctionField Point CoordinateRing.basis"
namespace CoordinateRing
p2m_export "WeierstrassCurve.Affine.CoordinateRing" "mk"
p2m_open "WeierstrassCurve.Affine.CoordinateRing WeierstrassCurve.Affine WeierstrassCurve"

open scoped nonZeroDivisors Polynomial
p2m_open "IsDedekindDomain P2MW.S_WeierstrassCurve_Affine_CoordinateRing_natDegree_norm_eq_finsum_count.IsDedekindDomain"

variable {K : Type*} [Field K] [IsAlgClosed K] (W : Affine K) [IsDedekindDomain W.CoordinateRing]

open scoped Classical in

theorem natDegree_norm_eq_finsum_count_aux {a : W.CoordinateRing} (ha : a ≠ 0) :
    ((Algebra.norm K[X] a).natDegree : ℤ) =
      ∑ᶠ v : HeightOneSpectrum W.CoordinateRing, FractionalIdeal.count W.FunctionField v
        (FractionalIdeal.spanSingleton W.CoordinateRing⁰
          (algebraMap W.CoordinateRing W.FunctionField a)) := by
  have hI : Ideal.span {a} ≠ ⊥ := by rwa [Ne, Ideal.span_singleton_eq_bot]
  haveI : Module.Finite K (W.CoordinateRing ⧸ Ideal.span {a}) :=
    Module.Finite.equiv
      ((Ideal.quotientEquivPiSpan (Ideal.span {a}) (CoordinateRing.basis W) hI).restrictScalars K).symm
  have hfin : Function.HasFiniteSupport fun v : HeightOneSpectrum W.CoordinateRing =>
      (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {a})).factors :=
    (Ideal.finite_factors hI).subset fun v hv =>
      (Associates.count_ne_zero_iff_dvd hI v.irreducible).mp (Function.mem_support.mp hv)
  have hcast := map_finsum (Nat.castAddMonoidHom ℤ) hfin
  rw [Nat.coe_castAddMonoidHom] at hcast
  rw [← finrank_quotient_span_eq_natDegree_norm (CoordinateRing.basis W) ha,
    finrank_quotient_eq_finsum_of_isAlgClosed K hI, hcast]
  refine finsum_congr fun v => ?_
  rw [← FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.count_coe _ _ hI]

end WeierstrassCurve.Affine.CoordinateRing

open scoped nonZeroDivisors

theorem solution {K : Type*} [Field K] [IsAlgClosed K] (W : WeierstrassCurve K) [IsDedekindDomain W.toAffine.CoordinateRing] {a : W.toAffine.CoordinateRing} (ha : a ≠ 0) : ((Algebra.norm (Polynomial K) a).natDegree : ℤ) = ∑ᶠ v : IsDedekindDomain.HeightOneSpectrum W.toAffine.CoordinateRing, FractionalIdeal.count W.toAffine.FunctionField v (FractionalIdeal.spanSingleton W.toAffine.CoordinateRing⁰ (algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField a)) :=
  WeierstrassCurve.Affine.CoordinateRing.natDegree_norm_eq_finsum_count_aux W.toAffine ha

end S_WeierstrassCurve_Affine_CoordinateRing_natDegree_norm_eq_finsum_count
end P2MW
export P2MW.S_WeierstrassCurve_Affine_CoordinateRing_natDegree_norm_eq_finsum_count (solution)
