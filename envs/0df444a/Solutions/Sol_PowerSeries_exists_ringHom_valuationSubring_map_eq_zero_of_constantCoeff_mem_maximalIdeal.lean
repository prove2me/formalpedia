-- Prove2me | solution 1 for PowerSeries.exists_ringHom_valuationSubring_map_eq_zero_of_constantCoeff_mem_maximalIdeal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/a8b7124e-f9d2-5295-88be-930c5ff760df

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PowerSeries_exists_ringHom_valuationSubring_map_eq_zero_of_constantCoeff_mem_maximalIdeal

namespace PowerSeries
p2m_export "PowerSeries" "IsWeierstrassFactorizationAt.algEquivQuotient_apply IsWeierstrassFactorizationAt isUnit_constantCoeff mk exists_isWeierstrassFactorization aeval eq_X_mul_shift_add_const C_eq_algebraMap IsWeierstrassFactorizationAt.algEquivQuotient constantCoeff IsWeierstrassFactorization coe_one coe_X weierstrassUnit ext map C coeff X weierstrassDistinguished isWeierstrassFactorization_weierstrassDistinguished_weierstrassUnit"
namespace WeierstrassZero
p2m_open "PowerSeries"

open Polynomial IsLocalRing

variable {A : Type*} [CommRing A]

theorem valuation_root_lt_one {Ω : Type*} [Field Ω] [Algebra A Ω] (V : ValuationSubring Ω)
    {I : Ideal A} (hdom : ∀ a ∈ I, algebraMap A Ω a ∈ V.nonunits)
    {P : A[X]} (hP : P.IsDistinguishedAt I)
    {t : Ω} (ht : Polynomial.aeval t P = 0) : V.valuation t < 1 := by
  by_contra hlt
  rw [not_lt] at hlt
  set v := V.valuation with hv
  have ht0 : t ≠ 0 := by
    rintro rfl
    simp at hlt
  have hvt0 : v t ≠ 0 := by simpa using ht0

  have hsum : Polynomial.aeval t P =
      ∑ i ∈ Finset.range (P.natDegree + 1), algebraMap A Ω (P.coeff i) * t ^ i := by
    rw [Polynomial.aeval_eq_sum_range]
    simp [Algebra.smul_def]
  rw [Finset.sum_range_succ, hP.monic.coeff_natDegree, map_one, one_mul] at hsum
  set n := P.natDegree with hn
  have hpow : t ^ n = -∑ i ∈ Finset.range n, algebraMap A Ω (P.coeff i) * t ^ i := by
    have := ht
    rw [hsum] at this
    linear_combination this

  have hterm : ∀ i ∈ Finset.range n, v (algebraMap A Ω (P.coeff i) * t ^ i) < v t ^ n := by
    intro i hi
    have hi' : i < n := Finset.mem_range.mp hi
    have hcoeff : v (algebraMap A Ω (P.coeff i)) < 1 :=
      (ValuationSubring.mem_nonunits_iff (A := V)).mp (hdom _ (hP.mem hi'))
    have hle : v t ^ i ≤ v t ^ n := pow_le_pow_right₀ hlt hi'.le
    have hne : v t ^ n ≠ 0 := pow_ne_zero _ hvt0
    calc v (algebraMap A Ω (P.coeff i) * t ^ i)
        = v (algebraMap A Ω (P.coeff i)) * v t ^ i := by rw [map_mul, map_pow]
      _ ≤ v (algebraMap A Ω (P.coeff i)) * v t ^ n := by gcongr
      _ < 1 * v t ^ n := by
          exact mul_lt_mul_of_pos_right hcoeff (pos_iff_ne_zero.mpr hne)
      _ = v t ^ n := one_mul _
  have hlt' : v (∑ i ∈ Finset.range n, algebraMap A Ω (P.coeff i) * t ^ i) < v t ^ n :=
    Valuation.map_sum_lt v (pow_ne_zero _ hvt0) hterm
  have : v (t ^ n) < v t ^ n := by
    rw [hpow, Valuation.map_neg]
    exact hlt'
  rw [map_pow] at this
  exact lt_irrefl _ this

variable [IsLocalRing A]

theorem natDegree_pos_of_isWeierstrassFactorization {F : A⟦X⟧} {P : A[X]} {u : A⟦X⟧}
    (H : F.IsWeierstrassFactorization P u) (hF₀ : PowerSeries.constantCoeff F ∈ maximalIdeal A) :
    0 < P.natDegree := by
  rw [Nat.pos_iff_ne_zero]
  intro h0
  have hP1 : P = 1 := by
    exact Polynomial.eq_one_of_monic_natDegree_zero H.isDistinguishedAt.monic h0
  have hunit : IsUnit F := by
    rw [H.eq_mul, hP1, Polynomial.coe_one, one_mul]
    exact H.isUnit
  have : IsUnit (PowerSeries.constantCoeff F) := PowerSeries.isUnit_constantCoeff F hunit
  exact (IsLocalRing.mem_maximalIdeal _ |>.mp hF₀) this

end PowerSeries.WeierstrassZero

open PowerSeries.WeierstrassZero Polynomial IsLocalRing in
theorem solution
    {A : Type*} [CommRing A] [IsLocalRing A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (F : PowerSeries A) (hF₀ : PowerSeries.constantCoeff F ∈ IsLocalRing.maximalIdeal A)
    (hF : PowerSeries.map (IsLocalRing.residue A) F ≠ 0)
    {Ω : Type*} [Field Ω] [IsAlgClosed Ω] [Algebra A Ω] (V : ValuationSubring Ω)
    (hAV : ∀ a : A, algebraMap A Ω a ∈ V)
    (hdom : ∀ a ∈ IsLocalRing.maximalIdeal A, algebraMap A Ω a ∈ V.nonunits) :
    ∃ φ : PowerSeries A →+* V,
      (∀ a : A, (φ (PowerSeries.C a) : Ω) = algebraMap A Ω a) ∧
      φ PowerSeries.X ∈ IsLocalRing.maximalIdeal V ∧
      (∀ G : PowerSeries A, PowerSeries.constantCoeff G ∈ IsLocalRing.maximalIdeal A →
        φ G ∈ IsLocalRing.maximalIdeal V) ∧
      (∀ G : PowerSeries A, IsLocalRing.residue V (φ G) =
        IsLocalRing.residue V (φ (PowerSeries.C (PowerSeries.constantCoeff G)))) ∧
      IsIntegral A (φ PowerSeries.X : Ω) ∧
      (∀ G : PowerSeries A, (φ G : Ω) ∈ Algebra.adjoin A {(φ PowerSeries.X : Ω)}) ∧
      φ F = 0 := by
  classical

  have H := F.isWeierstrassFactorization_weierstrassDistinguished_weierstrassUnit hF
  set P : A[X] := F.weierstrassDistinguished hF with hPdef
  set u : PowerSeries A := F.weierstrassUnit hF with hudef
  have hPdist : P.IsDistinguishedAt (maximalIdeal A) := H.isDistinguishedAt
  have hPmonic : P.Monic := hPdist.monic
  have hdeg : 0 < P.natDegree := natDegree_pos_of_isWeierstrassFactorization H hF₀

  obtain ⟨t₀, ht₀⟩ : ∃ t : Ω, Polynomial.aeval t P = 0 := by
    have hd : (P.map (algebraMap A Ω)).degree ≠ 0 := by
      rw [Polynomial.Monic.degree_map hPmonic]
      exact fun h => (Nat.pos_iff_ne_zero.mp hdeg)
        (Polynomial.natDegree_eq_zero_iff_degree_le_zero.mpr h.le)
    obtain ⟨t, ht⟩ := IsAlgClosed.exists_root _ hd
    exact ⟨t, by rwa [Polynomial.aeval_def, ← Polynomial.eval_map]⟩
  have hvt₀ : V.valuation t₀ < 1 := valuation_root_lt_one V hdom hPdist ht₀
  have ht₀V : t₀ ∈ V := V.mem_of_valuation_le_one _ hvt₀.le
  have ht₀nu : t₀ ∈ V.nonunits := (ValuationSubring.mem_nonunits_iff (A := V)).mpr hvt₀

  set e := H.algEquivQuotient with hedef
  have hker : ∀ a ∈ Ideal.span ({P} : Set A[X]), Polynomial.aeval t₀ a = 0 := by
    intro a ha
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    simp [ht₀]
  set ψ₀ : (A[X] ⧸ Ideal.span ({P} : Set A[X])) →ₐ[A] Ω :=
    Ideal.Quotient.liftₐ (Ideal.span ({P} : Set A[X])) (Polynomial.aeval t₀) hker with hψ₀def
  have hψ₀mk : ∀ r : A[X], ψ₀ (Ideal.Quotient.mk _ r) = Polynomial.aeval t₀ r := fun r => rfl
  set ψ : PowerSeries A →ₐ[A] Ω :=
    (ψ₀.comp (e.symm : (PowerSeries A ⧸ Ideal.span ({F} : Set (PowerSeries A))) →ₐ[A]
      (A[X] ⧸ Ideal.span ({P} : Set A[X])))).comp
      (Ideal.Quotient.mkₐ A (Ideal.span ({F} : Set (PowerSeries A)))) with hψdef
  have hψapply : ∀ G : PowerSeries A, ψ G = ψ₀ (e.symm (Ideal.Quotient.mk _ G)) := fun G => rfl

  have he_mk : ∀ r : A[X], e (Ideal.Quotient.mk _ r) = Ideal.Quotient.mk _ (r : PowerSeries A) := by
    intro r
    rw [hedef, PowerSeries.IsWeierstrassFactorizationAt.algEquivQuotient_apply,
      Ideal.quotientMapₐ]
    simp [Ideal.quotientMap_mk, Ideal.quotientEquivAlgOfEq_mk]
  have hψcoe : ∀ r : A[X], ψ (r : PowerSeries A) = Polynomial.aeval t₀ r := by
    intro r
    rw [hψapply, ← he_mk, AlgEquiv.symm_apply_apply, hψ₀mk]
  have hψX : ψ PowerSeries.X = t₀ := by
    have := hψcoe Polynomial.X
    rwa [Polynomial.coe_X, Polynomial.aeval_X] at this
  have hψC : ∀ a : A, ψ (PowerSeries.C a) = algebraMap A Ω a := by
    intro a
    rw [PowerSeries.C_eq_algebraMap, AlgHom.commutes]

  have hψpoly : ∀ G : PowerSeries A, ∃ r : A[X], ψ G = Polynomial.aeval t₀ r := by
    intro G
    obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (e.symm (Ideal.Quotient.mk _ G))
    refine ⟨r, ?_⟩
    rw [hψapply, ← hr, hψ₀mk]
  have hψmem : ∀ G : PowerSeries A, ψ G ∈ V := by
    intro G
    obtain ⟨r, hr⟩ := hψpoly G
    rw [hr]
    have hrange : Polynomial.aeval t₀ r ∈ Algebra.adjoin A {t₀} := by
      rw [Algebra.adjoin_singleton_eq_range_aeval]; exact ⟨r, rfl⟩

    have hadj : (Algebra.adjoin A {t₀} : Subalgebra A Ω) ≤
        { carrier := V, mul_mem' := V.mul_mem _ _, one_mem' := V.one_mem,
          add_mem' := V.add_mem _ _, zero_mem' := V.zero_mem,
          algebraMap_mem' := hAV } := by
      rw [Algebra.adjoin_le_iff]
      rintro _ rfl
      exact ht₀V
    exact hadj hrange
  have hψF : ψ F = 0 := by
    rw [hψapply]
    have : (Ideal.Quotient.mk (Ideal.span ({F} : Set (PowerSeries A))) F) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self F)
    rw [this, map_zero, map_zero]

  let φ : PowerSeries A →+* V := (ψ : PowerSeries A →+* Ω).codRestrict V hψmem
  have hφ : ∀ G, (φ G : Ω) = ψ G := fun G => rfl
  have hφX : φ PowerSeries.X ∈ maximalIdeal V := by
    rw [← ValuationSubring.coe_mem_nonunits_iff, hφ, hψX]
    exact ht₀nu
  have hmax : ∀ G : PowerSeries A, PowerSeries.constantCoeff G ∈ maximalIdeal A →
      φ G ∈ maximalIdeal V := by
    intro G hG

    rw [PowerSeries.eq_X_mul_shift_add_const G, map_add, map_mul]
    refine Ideal.add_mem _ (Ideal.mul_mem_right _ _ hφX) ?_
    rw [← ValuationSubring.coe_mem_nonunits_iff, hφ, hψC]
    exact hdom _ hG
  refine ⟨φ, ?_, hφX, hmax, ?_, ?_, ?_, ?_⟩
  · intro a
    rw [hφ, hψC]
  · intro G
    rw [← sub_eq_zero, ← map_sub, ← map_sub, IsLocalRing.residue_eq_zero_iff]
    exact hmax _ (by simp)
  · refine ⟨P, hPmonic, ?_⟩
    rw [hφ, hψX, ← Polynomial.aeval_def, ht₀]
  · intro G
    obtain ⟨r, hr⟩ := hψpoly G
    rw [hφ, hφ, hψX, hr, Algebra.adjoin_singleton_eq_range_aeval]
    exact ⟨r, rfl⟩
  · exact Subtype.ext (by rw [hφ, hψF]; rfl)

end S_PowerSeries_exists_ringHom_valuationSubring_map_eq_zero_of_constantCoeff_mem_maximalIdeal
end P2MW
export P2MW.S_PowerSeries_exists_ringHom_valuationSubring_map_eq_zero_of_constantCoeff_mem_maximalIdeal (solution)
