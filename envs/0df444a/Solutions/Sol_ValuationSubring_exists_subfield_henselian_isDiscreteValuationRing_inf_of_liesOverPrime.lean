-- Prove2me | solution 1 for ValuationSubring.exists_subfield_henselian_isDiscreteValuationRing_inf_of_liesOverPrime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/799dc946-8f79-5a8f-b026-56ce0cc2cc30

import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import Theorems.Thm_ValuationSubring_isDiscreteValuationRing_comap_fixedField_inertiaSubgroupIn
import Theorems.Thm_ValuationSubring_henselianLocalRing_comap_fixedField_inertiaSubgroupIn
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField_comap_fixedField_inertiaSubgroupIn
import Theorems.Thm_ValuationSubring_isDiscreteValuationRing_and_henselianLocalRing_comap_of_finiteDimensional
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_exists_subfield_henselian_isDiscreteValuationRing_inf_of_liesOverPrime
p2m_attr_erase "instance" "AlgebraicClosure.Rat.isGalois"

set_option autoImplicit false

open IsLocalRing Polynomial

namespace P2M
namespace TameBase

variable (A : ValuationSubring (AlgebraicClosure ℚ))

noncomputable abbrev T : IntermediateField ℚ (AlgebraicClosure ℚ) :=
  IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)

noncomputable abbrev OT : ValuationSubring ↥(T A) := A.comap (algebraMap ↥(T A) (AlgebraicClosure ℚ))

noncomputable def inclT : ↥(OT A) →+* ↥A :=
  (algebraMap ↥(T A) (AlgebraicClosure ℚ)).restrict (OT A).toSubring A.toSubring (fun _ hx => hx)

@[scoped simp] theorem coe_inclT (x : ↥(OT A)) :
    ((inclT A x : ↥A) : AlgebraicClosure ℚ) = ((x : ↥(T A)) : AlgebraicClosure ℚ) :=
  rfl

scoped instance : IsLocalHom (inclT A) := by
  constructor
  intro x hx
  have hx0 : ((x : ↥(T A)) : AlgebraicClosure ℚ) ≠ 0 := by
    intro h0
    apply hx.ne_zero
    exact Subtype.ext h0
  have hxK : (x : ↥(T A)) ≠ 0 := fun h => hx0 (by rw [h]; rfl)
  obtain ⟨u, hu⟩ := hx
  have hinvA : ((x : ↥(T A)) : AlgebraicClosure ℚ)⁻¹ ∈ A := by
    have e : ((↑(u⁻¹) : ↥A) : AlgebraicClosure ℚ) = ((x : ↥(T A)) : AlgebraicClosure ℚ)⁻¹ := by
      apply eq_inv_of_mul_eq_one_left
      have := congrArg (fun z : ↥A => (z : AlgebraicClosure ℚ)) u.inv_mul
      simpa [hu] using this
    rw [← e]; exact (↑(u⁻¹) : ↥A).2
  have hinvO : (x : ↥(T A))⁻¹ ∈ OT A := by
    show algebraMap ↥(T A) (AlgebraicClosure ℚ) (x : ↥(T A))⁻¹ ∈ A
    rw [map_inv₀]; exact hinvA
  refine ⟨⟨x, ⟨_, hinvO⟩, ?_, ?_⟩, rfl⟩
  · exact Subtype.ext (mul_inv_cancel₀ hxK)
  · exact Subtype.ext (inv_mul_cancel₀ hxK)

variable (K : IntermediateField ↥(T A) (AlgebraicClosure ℚ))

noncomputable abbrev OK : ValuationSubring ↥K := A.comap (algebraMap ↥K (AlgebraicClosure ℚ))

noncomputable def inclK : ↥(OK A K) →+* ↥A :=
  (algebraMap ↥K (AlgebraicClosure ℚ)).restrict (OK A K).toSubring A.toSubring (fun _ hx => hx)

@[scoped simp] theorem coe_inclK (x : ↥(OK A K)) :
    ((inclK A K x : ↥A) : AlgebraicClosure ℚ) = ((x : ↥K) : AlgebraicClosure ℚ) :=
  rfl

scoped instance : IsLocalHom (inclK A K) := by
  constructor
  intro x hx
  have hx0 : ((x : ↥K) : AlgebraicClosure ℚ) ≠ 0 := by
    intro h0
    apply hx.ne_zero
    exact Subtype.ext h0
  have hxK : (x : ↥K) ≠ 0 := fun h => hx0 (by rw [h]; rfl)
  obtain ⟨u, hu⟩ := hx
  have hinvA : ((x : ↥K) : AlgebraicClosure ℚ)⁻¹ ∈ A := by
    have e : ((↑(u⁻¹) : ↥A) : AlgebraicClosure ℚ) = ((x : ↥K) : AlgebraicClosure ℚ)⁻¹ := by
      apply eq_inv_of_mul_eq_one_left
      have := congrArg (fun z : ↥A => (z : AlgebraicClosure ℚ)) u.inv_mul
      simpa [hu] using this
    rw [← e]; exact (↑(u⁻¹) : ↥A).2
  have hinvO : (x : ↥K)⁻¹ ∈ OK A K := by
    show algebraMap ↥K (AlgebraicClosure ℚ) (x : ↥K)⁻¹ ∈ A
    rw [map_inv₀]; exact hinvA
  refine ⟨⟨x, ⟨_, hinvO⟩, ?_, ?_⟩, rfl⟩
  · exact Subtype.ext (mul_inv_cancel₀ hxK)
  · exact Subtype.ext (inv_mul_cancel₀ hxK)

theorem natCast_mem_maximalIdeal (q : ℕ) (hA : A.LiesOverPrime q) :
    ((q : ↥A)) ∈ maximalIdeal ↥A := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  rintro ⟨u, hu⟩
  have h1 : A.valuation ((u : ↥A) : AlgebraicClosure ℚ) = 1 := A.valuation_unit u
  rw [hu] at h1
  have h2 : A.valuation (q : AlgebraicClosure ℚ) < 1 := (ValuationSubring.mem_nonunits_iff (A := A)).mp hA
  have e : ((q : ↥A) : AlgebraicClosure ℚ) = (q : AlgebraicClosure ℚ) := by simp
  rw [e] at h1
  exact h2.ne h1

theorem exists_sub_mem (q : ℕ) [Fact q.Prime] (hA : A.LiesOverPrime q)
    (hres : IsAlgClosed (ResidueField ↥(OT A)))
    (a : AlgebraicClosure ℚ) (ha : a ∈ A) :
    ∃ c : ↥(T A), (c : AlgebraicClosure ℚ) ∈ A ∧ ∃ h : a - c ∈ A, (⟨_, h⟩ : ↥A) ∈ maximalIdeal ↥A := by
  classical

  let ρ : ResidueField ↥(OT A) →+* ResidueField ↥A := IsLocalRing.ResidueField.map (inclT A)
  letI : Algebra (ResidueField ↥(OT A)) (ResidueField ↥A) := ρ.toAlgebra

  obtain ⟨p, hp0, hpa⟩ : IsAlgebraic ℤ a := by
    have halg : IsAlgebraic ℚ a := by
      have : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := by
        convert AlgebraicClosure.isAlgebraic ℚ <;> first | rfl | exact Subsingleton.elim _ _
      exact Algebra.IsAlgebraic.isAlgebraic a
    exact (IsFractionRing.isAlgebraic_iff ℤ ℚ (AlgebraicClosure ℚ)).mpr halg
  set p₁ : ℤ[X] := p.primPart with hp₁
  have hp₁a : aeval a p₁ = 0 := by
    rw [aeval_def] at hpa ⊢
    exact eval₂_primPart_eq_zero (RingHom.injective_int (algebraMap ℤ (AlgebraicClosure ℚ))) hp0 hpa
  have hprim : p₁.IsPrimitive := isPrimitive_primPart p

  set pO : (ResidueField ↥(OT A))[X] := p₁.map (algebraMap ℤ (ResidueField ↥(OT A))) with hpO
  have hqO : ((q : ↥(OT A))) ∈ maximalIdeal ↥(OT A) := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have h := natCast_mem_maximalIdeal A q hA
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at h
    apply h
    have := hu.map (inclT A)
    rwa [map_natCast] at this
  haveI : CharP (ResidueField ↥(OT A)) q := by
    rw [CharP.charP_iff_prime_eq_zero Fact.out, ← map_natCast (IsLocalRing.residue ↥(OT A)),
      IsLocalRing.residue_eq_zero_iff]
    exact hqO
  have hpO0 : pO ≠ 0 := by
    intro h0
    have hdvd : ∀ n, (q : ℤ) ∣ p₁.coeff n := by
      intro n
      have hc : algebraMap ℤ (ResidueField ↥(OT A)) (p₁.coeff n) = 0 := by
        have := congrArg (fun r => r.coeff n) h0
        simpa [hpO, coeff_map] using this
      rw [eq_intCast] at hc
      exact (CharP.intCast_eq_zero_iff (ResidueField ↥(OT A)) q (p₁.coeff n)).mp hc
    have hCd : C (q : ℤ) ∣ p₁ := (C_dvd_iff_dvd_coeff (q : ℤ) p₁).mpr hdvd
    have hu : IsUnit (q : ℤ) := hprim (q : ℤ) hCd
    rw [Int.isUnit_iff_natAbs_eq, Int.natAbs_natCast] at hu
    exact (Fact.out : q.Prime).one_lt.ne' hu

  set abar : ResidueField ↥A := IsLocalRing.residue ↥A ⟨a, ha⟩ with habar
  have hroot : aeval abar pO = 0 := by
    have emap : pO.map ρ = p₁.map (algebraMap ℤ (ResidueField ↥A)) := by
      rw [hpO, Polynomial.map_map]
      congr 1
    rw [aeval_def, show algebraMap (ResidueField ↥(OT A)) (ResidueField ↥A) = ρ from rfl, ← eval_map, emap,
      eval_map, ← aeval_def]
    have h1 : (aeval (⟨a, ha⟩ : ↥A) p₁ : ↥A) = 0 := by
      apply Subtype.val_injective
      have := aeval_algHom_apply ((A.subtype).toIntAlgHom) (⟨a, ha⟩ : ↥A) p₁
      simp only [RingHom.toIntAlgHom_apply, ValuationSubring.coe_subtype] at this
      show ((aeval (⟨a, ha⟩ : ↥A) p₁ : ↥A) : AlgebraicClosure ℚ) = ((0 : ↥A) : AlgebraicClosure ℚ)
      rw [← this]
      first | exact hp₁a | simpa using hp₁a
    have h2 := aeval_algHom_apply ((IsLocalRing.residue ↥A).toIntAlgHom) (⟨a, ha⟩ : ↥A) p₁
    simp only [RingHom.toIntAlgHom_apply] at h2
    have h3 := h2.trans (by rw [h1, map_zero])
    rw [habar]
    convert h3 using 2 <;> rfl

  have halgO : IsAlgebraic (ResidueField ↥(OT A)) abar := ⟨pO, hpO0, hroot⟩
  have hint : IsIntegral (ResidueField ↥(OT A)) abar := halgO.isIntegral
  have hdeg : (minpoly (ResidueField ↥(OT A)) abar).degree = 1 :=
    IsAlgClosed.degree_eq_one_of_irreducible _ (minpoly.irreducible hint)
  obtain ⟨cbar, hcbar⟩ := minpoly.mem_range_of_degree_eq_one (ResidueField ↥(OT A)) abar hdeg
  obtain ⟨c, rfl⟩ := IsLocalRing.residue_surjective cbar
  have e : IsLocalRing.residue ↥A (inclT A c) = abar := by
    rw [← hcbar]
    show _ = ρ (IsLocalRing.residue ↥(OT A) c)
    exact (IsLocalRing.ResidueField.map_residue (inclT A) c).symm
  refine ⟨(c : ↥(T A)), c.2, sub_mem ha c.2, ?_⟩
  have hsub : (⟨a - ((c : ↥(T A)) : AlgebraicClosure ℚ), sub_mem ha c.2⟩ : ↥A) = ⟨a, ha⟩ - inclT A c :=
    Subtype.ext rfl
  rw [hsub, ← Ideal.Quotient.mk_eq_mk_iff_sub_mem]
  exact e.symm

theorem sum_eq_zero_or_exists {R Γ₀ : Type*} [CommRing R] [LinearOrderedCommGroupWithZero Γ₀]
    (v : Valuation R Γ₀) {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → R)
    (hinj : ∀ i ∈ s, ∀ j ∈ s, f i ≠ 0 → f j ≠ 0 → v (f i) = v (f j) → i = j) :
    (∑ i ∈ s, f i) = 0 ∨ ∃ j ∈ s, f j ≠ 0 ∧ v (∑ i ∈ s, f i) = v (f j) := by
  induction s using Finset.induction_on with
  | empty => left; simp
  | @insert a s ha ih =>
    have hinj' : ∀ i ∈ s, ∀ j ∈ s, f i ≠ 0 → f j ≠ 0 → v (f i) = v (f j) → i = j :=
      fun i hi j hj => hinj i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj)
    rw [Finset.sum_insert ha]
    rcases ih hinj' with h0 | ⟨j, hj, hj0, hvj⟩
    · rw [h0, add_zero]
      by_cases hfa : f a = 0
      · left; exact hfa
      · right; exact ⟨a, Finset.mem_insert_self a s, hfa, rfl⟩
    · by_cases hfa : f a = 0
      · right
        refine ⟨j, Finset.mem_insert_of_mem hj, hj0, ?_⟩
        rw [hfa, zero_add, hvj]
      · have hne : v (f a) ≠ v (∑ i ∈ s, f i) := by
          rw [hvj]
          intro h
          have := hinj a (Finset.mem_insert_self a s) j (Finset.mem_insert_of_mem hj) hfa hj0 h
          exact ha (this ▸ hj)
        right
        rw [Valuation.map_add_of_distinct_val v hne]
        rcases le_total (v (f a)) (v (∑ i ∈ s, f i)) with hle | hle
        · rw [max_eq_right hle, hvj]
          exact ⟨j, Finset.mem_insert_of_mem hj, hj0, rfl⟩
        · rw [max_eq_left hle]
          exact ⟨a, Finset.mem_insert_self a s, hfa, rfl⟩

theorem eq_one_of_mul_eq_one_of_le {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] {a b : Γ₀}
    (ha : a ≤ 1) (hb : b ≤ 1) (hab : a * b = 1) : a = 1 := by
  refine le_antisymm ha ?_
  calc (1 : Γ₀) = a * b := hab.symm
    _ ≤ a * 1 := mul_le_mul_right hb a
    _ = a := mul_one a

theorem valuation_unit_OT (u : (↥(OT A))ˣ) :
    A.valuation (((u : ↥(OT A)) : ↥(T A)) : AlgebraicClosure ℚ) = 1 := by
  let e : ↥(OT A) →+* AlgebraicClosure ℚ := (algebraMap ↥(T A) (AlgebraicClosure ℚ)).comp (OT A).subtype
  have h1 : e (u : ↥(OT A)) * e (↑(u⁻¹) : ↥(OT A)) = 1 := by
    rw [← map_mul, u.mul_inv, map_one]
  have hle1 : A.valuation (e (u : ↥(OT A))) ≤ 1 := (A.valuation_le_one_iff _).mpr (u : ↥(OT A)).2
  have hle2 : A.valuation (e (↑(u⁻¹) : ↥(OT A))) ≤ 1 := (A.valuation_le_one_iff _).mpr (↑(u⁻¹) : ↥(OT A)).2
  have h2 : A.valuation (e (u : ↥(OT A))) = 1 :=
    eq_one_of_mul_eq_one_of_le hle1 hle2 (by rw [← map_mul, h1, map_one])
  exact h2

theorem exists_valuation_eq_pow_of_mem (q : ℕ)
    (hdvr : IsDiscreteValuationRing ↥(OT A)) (hirr : Irreducible ((q : ℕ) : ↥(OT A)))
    (t : ↥(T A)) (ht0 : (t : AlgebraicClosure ℚ) ≠ 0) (htA : (t : AlgebraicClosure ℚ) ∈ A) :
    ∃ m : ℕ, A.valuation (t : AlgebraicClosure ℚ) = A.valuation (q : AlgebraicClosure ℚ) ^ m := by
  have htO : t ∈ OT A := htA
  have ht0' : (⟨t, htO⟩ : ↥(OT A)) ≠ 0 := by
    intro h
    apply ht0
    have := congrArg (fun z : ↥(OT A) => ((z : ↥(T A)) : AlgebraicClosure ℚ)) h
    simpa using this
  obtain ⟨m, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ht0' hirr
  refine ⟨m, ?_⟩
  have hcoe : (t : AlgebraicClosure ℚ) =
      (((u : ↥(OT A)) : ↥(T A)) : AlgebraicClosure ℚ) * (q : AlgebraicClosure ℚ) ^ m := by
    have := congrArg (fun z : ↥(OT A) => ((inclT A z : ↥A) : AlgebraicClosure ℚ)) hu
    simpa using this
  rw [hcoe, map_mul, map_pow, valuation_unit_OT, one_mul]

theorem exists_valuation_eq_zpow_T (q : ℕ)
    (hdvr : IsDiscreteValuationRing ↥(OT A)) (hirr : Irreducible ((q : ℕ) : ↥(OT A)))
    (t : ↥(T A)) (ht0 : (t : AlgebraicClosure ℚ) ≠ 0) :
    ∃ k : ℤ, A.valuation (t : AlgebraicClosure ℚ) = A.valuation (q : AlgebraicClosure ℚ) ^ k := by
  by_cases htA : (t : AlgebraicClosure ℚ) ∈ A
  · obtain ⟨m, hm⟩ := exists_valuation_eq_pow_of_mem A q hdvr hirr t ht0 htA
    exact ⟨m, by rw [hm, zpow_natCast]⟩
  · have htinv : (t : AlgebraicClosure ℚ)⁻¹ ∈ A := (A.mem_or_inv_mem _).resolve_left htA
    have ht0i : ((t⁻¹ : ↥(T A)) : AlgebraicClosure ℚ) ≠ 0 := by
      rw [show ((t⁻¹ : ↥(T A)) : AlgebraicClosure ℚ) = (t : AlgebraicClosure ℚ)⁻¹ from by simp]
      exact inv_ne_zero ht0
    have htiA : ((t⁻¹ : ↥(T A)) : AlgebraicClosure ℚ) ∈ A := by
      rw [show ((t⁻¹ : ↥(T A)) : AlgebraicClosure ℚ) = (t : AlgebraicClosure ℚ)⁻¹ from by simp]
      exact htinv
    obtain ⟨m, hm⟩ := exists_valuation_eq_pow_of_mem A q hdvr hirr t⁻¹ ht0i htiA
    refine ⟨-(m : ℤ), ?_⟩
    rw [show ((t⁻¹ : ↥(T A)) : AlgebraicClosure ℚ) = (t : AlgebraicClosure ℚ)⁻¹ from by simp, map_inv₀] at hm
    rw [zpow_neg, zpow_natCast, ← hm, inv_inv]

theorem exists_valuation_eq_zpow_layer (q : ℕ) [Fact q.Prime] (hA : A.LiesOverPrime q)
    (hdvr : IsDiscreteValuationRing ↥(OT A)) (hirr : Irreducible ((q : ℕ) : ↥(OT A)))
    (π : AlgebraicClosure ℚ) (hπ : π ^ (q ^ 2 - 1) = (q : AlgebraicClosure ℚ))
    (x : AlgebraicClosure ℚ) (hx : x ∈ IntermediateField.adjoin ↥(T A) {π}) (hx0 : x ≠ 0) :
    ∃ m : ℤ, A.valuation x = A.valuation π ^ m := by
  classical

  set n : ℕ := q ^ 2 - 1 with hn
  have hq2 : 2 ≤ q := (Fact.out : q.Prime).two_le
  have hn0 : n ≠ 0 := by
    have : 4 ≤ q ^ 2 := by nlinarith
    omega
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
  have hq0 : (q : AlgebraicClosure ℚ) ≠ 0 := by exact_mod_cast (Fact.out : q.Prime).ne_zero
  have hπ0 : π ≠ 0 := by
    intro h
    rw [h, zero_pow hn0] at hπ
    exact hq0 hπ.symm

  have hvq : A.valuation (q : AlgebraicClosure ℚ) < 1 := (ValuationSubring.mem_nonunits_iff (A := A)).mp hA
  have hvπn : A.valuation π ^ n = A.valuation (q : AlgebraicClosure ℚ) := by rw [← map_pow, hπ]
  have hvπ0 : 0 < A.valuation π := zero_lt_iff.mpr ((Valuation.ne_zero_iff A.valuation).mpr hπ0)
  have hvπ1 : A.valuation π < 1 := by
    by_contra h
    push Not at h
    have : 1 ≤ A.valuation π ^ n := one_le_pow_of_one_le' h n
    rw [hvπn] at this
    exact absurd hvq (not_lt.mpr this)

  have hπint : IsIntegral ↥(T A) π := by
    refine ⟨X ^ n - C (q : ↥(T A)), monic_X_pow_sub_C _ hn0, ?_⟩
    simp [hπ]
  have hxalg : x ∈ Algebra.adjoin ↥(T A) {π} := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hπint.isAlgebraic]
    exact hx
  rw [Algebra.adjoin_singleton_eq_range_aeval, AlgHom.mem_range] at hxalg
  obtain ⟨p, rfl⟩ := hxalg
  set r : (↥(T A))[X] := p %ₘ minpoly ↥(T A) π with hr
  have hrp : aeval π r = aeval π p := aeval_modByMonic_eq_self_of_root (minpoly.aeval _ _)
  have hrdeg : r.natDegree < n := by
    by_cases hr0 : r = 0
    · rw [hr0, natDegree_zero]; exact hnpos
    have h1 : r.degree < (minpoly ↥(T A) π).degree := degree_modByMonic_lt p (minpoly.monic hπint)
    have hroot : aeval π (X ^ n - C (q : ↥(T A))) = 0 := by simp [hπ]
    have h2 : (minpoly ↥(T A) π).degree ≤ (X ^ n - C (q : ↥(T A))).degree :=
      degree_le_of_dvd (minpoly.dvd _ _ hroot) (X_pow_sub_C_ne_zero hnpos _)
    rw [degree_X_pow_sub_C hnpos] at h2
    exact (natDegree_lt_iff_degree_lt hr0).mpr (h1.trans_le h2)

  have hterm : ∀ i : ℕ, r.coeff i • π ^ i ≠ 0 →
      ∃ k : ℤ, A.valuation (r.coeff i • π ^ i) = A.valuation π ^ ((n : ℤ) * k + i) := by
    intro i hi
    have hc0 : ((r.coeff i : ↥(T A)) : AlgebraicClosure ℚ) ≠ 0 := by
      intro h0
      apply hi
      rw [Algebra.smul_def, show algebraMap ↥(T A) (AlgebraicClosure ℚ) (r.coeff i) =
        ((r.coeff i : ↥(T A)) : AlgebraicClosure ℚ) from rfl, h0, zero_mul]
    obtain ⟨k, hk⟩ := exists_valuation_eq_zpow_T A q hdvr hirr (r.coeff i) hc0
    refine ⟨k, ?_⟩
    rw [Algebra.smul_def, show algebraMap ↥(T A) (AlgebraicClosure ℚ) (r.coeff i) =
        ((r.coeff i : ↥(T A)) : AlgebraicClosure ℚ) from rfl, map_mul, map_pow, hk, ← hvπn,
      ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_add₀ hvπ0.ne']

  have hinj : ∀ i ∈ Finset.range n, ∀ j ∈ Finset.range n,
      r.coeff i • π ^ i ≠ 0 → r.coeff j • π ^ j ≠ 0 →
        A.valuation (r.coeff i • π ^ i) = A.valuation (r.coeff j • π ^ j) → i = j := by
    intro i hi j hj hi0 hj0 hij
    obtain ⟨k, hk⟩ := hterm i hi0
    obtain ⟨l, hl⟩ := hterm j hj0
    rw [hk, hl] at hij
    have hexp : (n : ℤ) * k + i = (n : ℤ) * l + j := (zpow_right_injective₀ hvπ0 hvπ1.ne) hij
    have hi' : i < n := Finset.mem_range.mp hi
    have hj' : j < n := Finset.mem_range.mp hj
    have hdvd : (n : ℤ) ∣ ((i : ℤ) - j) := ⟨l - k, by linarith⟩
    have habs : |((i : ℤ) - j)| < n := by
      rw [abs_lt]; constructor <;> omega
    have := Int.eq_zero_of_abs_lt_dvd hdvd habs
    omega

  rw [← hrp, aeval_eq_sum_range' hrdeg]
  rcases sum_eq_zero_or_exists A.valuation (Finset.range n) (fun i => r.coeff i • π ^ i) hinj with h0 | ⟨j, hj, hj0, hvj⟩
  · exfalso
    apply hx0
    rw [← hrp, aeval_eq_sum_range' hrdeg]
    exact h0
  · obtain ⟨k, hk⟩ := hterm j hj0
    exact ⟨(n : ℤ) * k + j, hvj.trans hk⟩

end P2M.TameBase
p2m_reactivate "P2MW.S_ValuationSubring_exists_subfield_henselian_isDiscreteValuationRing_inf_of_liesOverPrime.P2M P2MW.S_ValuationSubring_exists_subfield_henselian_isDiscreteValuationRing_inf_of_liesOverPrime.P2M.TameBase"
p2m_reactivate "P2MW.S_ValuationSubring_exists_subfield_henselian_isDiscreteValuationRing_inf_of_liesOverPrime.P2M"

open P2M.TameBase in
theorem solution
    (q : ℕ) [Fact q.Prime]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (π : AlgebraicClosure ℚ) (hπ : π ^ (q ^ 2 - 1) = (q : AlgebraicClosure ℚ)) (hπP : π ∈ A) :
    ∃ (K₀ : Subfield (AlgebraicClosure ℚ)) (_ : Algebra.IsAlgebraic ↥K₀ (AlgebraicClosure ℚ))
      (A₀ : Type) (_ : CommRing A₀) (_ : IsDomain A₀) (_ : IsDiscreteValuationRing A₀) (_ : HenselianLocalRing A₀)
      (ι : A₀ →+* ↥A) (_ : IsLocalHom ι) (ϖ₀ : A₀),
      π ∈ K₀ ∧
      Function.Injective ι ∧
      Set.range (fun a : A₀ => ((ι a : ↥A) : AlgebraicClosure ℚ)) =
        (A : Set (AlgebraicClosure ℚ)) ∩ (K₀ : Set (AlgebraicClosure ℚ)) ∧
      Function.Surjective ((IsLocalRing.residue ↥A).comp ι) ∧
      maximalIdeal A₀ = Ideal.span {ϖ₀} ∧
      ((ι ϖ₀ : ↥A) : AlgebraicClosure ℚ) = π := by
  classical

  set n : ℕ := q ^ 2 - 1 with hn
  have hq2 : 2 ≤ q := (Fact.out : q.Prime).two_le
  have hn0 : n ≠ 0 := by
    have : 4 ≤ q ^ 2 := by nlinarith
    omega
  have hq0 : (q : AlgebraicClosure ℚ) ≠ 0 := by exact_mod_cast (Fact.out : q.Prime).ne_zero
  have hπ0 : π ≠ 0 := by
    intro h
    rw [h, zero_pow hn0] at hπ
    exact hq0 hπ.symm

  obtain ⟨hdvrT, hirrT, -, -⟩ :=
    ValuationSubring.isDiscreteValuationRing_comap_fixedField_inertiaSubgroupIn A q hA
  have hhensT : HenselianLocalRing ↥(OT A) :=
    ValuationSubring.henselianLocalRing_comap_fixedField_inertiaSubgroupIn (K := ℚ) A
  have hresT : IsAlgClosed (ResidueField ↥(OT A)) :=
    ValuationSubring.isAlgClosed_residueField_comap_fixedField_inertiaSubgroupIn A q hA ℚ

  have hπint : IsIntegral ↥(T A) π := by
    refine ⟨X ^ n - C (q : ↥(T A)), monic_X_pow_sub_C _ hn0, ?_⟩
    simp [hπ]
  set K : IntermediateField ↥(T A) (AlgebraicClosure ℚ) := IntermediateField.adjoin ↥(T A) {π} with hK
  haveI : FiniteDimensional ↥(T A) ↥K := IntermediateField.adjoin.finiteDimensional hπint
  have halgQ : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := by
    convert AlgebraicClosure.isAlgebraic ℚ <;> first | rfl | exact Subsingleton.elim _ _
  obtain ⟨hdvr, hhens⟩ :=
    ValuationSubring.isDiscreteValuationRing_and_henselianLocalRing_comap_of_finiteDimensional halgQ A (T A)
      hdvrT hhensT K inferInstance
  have hπK : π ∈ K := IntermediateField.mem_adjoin_simple_self _ π
  have hπO : (⟨π, hπK⟩ : ↥K) ∈ OK A K := hπP
  let ϖ₀ : ↥(OK A K) := ⟨⟨π, hπK⟩, hπO⟩

  have hvq : A.valuation (q : AlgebraicClosure ℚ) < 1 := (ValuationSubring.mem_nonunits_iff (A := A)).mp hA
  have hvπn : A.valuation π ^ n = A.valuation (q : AlgebraicClosure ℚ) := by rw [← map_pow, hπ]
  have hvπ0 : 0 < A.valuation π := zero_lt_iff.mpr ((Valuation.ne_zero_iff A.valuation).mpr hπ0)
  have hvπ1 : A.valuation π < 1 := by
    by_contra h
    push Not at h
    have : 1 ≤ A.valuation π ^ n := one_le_pow_of_one_le' h n
    rw [hvπn] at this
    exact absurd hvq (not_lt.mpr this)
  refine ⟨K.toSubfield, ?_, ↥(OK A K), inferInstance, inferInstance, hdvr, hhens, inclK A K, inferInstance, ϖ₀,
    ?_, ?_, ?_, ?_, ?_, rfl⟩
  ·
    refine ⟨fun x => ?_⟩
    obtain ⟨p, hp0, hpx⟩ : IsAlgebraic ℤ x :=
      (IsFractionRing.isAlgebraic_iff ℤ ℚ (AlgebraicClosure ℚ)).mpr (halgQ.isAlgebraic x)
    have hcomp : (algebraMap ↥K.toSubfield (AlgebraicClosure ℚ)).comp (algebraMap ℤ ↥K.toSubfield) =
        algebraMap ℤ (AlgebraicClosure ℚ) := Subsingleton.elim _ _
    have hinjZ : Function.Injective (algebraMap ℤ ↥K.toSubfield) := by
      apply Function.Injective.of_comp (f := algebraMap ↥K.toSubfield (AlgebraicClosure ℚ))
      rw [← RingHom.coe_comp, hcomp]
      exact RingHom.injective_int _
    refine ⟨p.map (algebraMap ℤ ↥K.toSubfield), (Polynomial.map_ne_zero_iff hinjZ).mpr hp0, ?_⟩
    rw [aeval_def, eval₂_map, hcomp, ← aeval_def, hpx]
  ·
    exact hπK
  ·
    intro a b h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : ↥A => (z : AlgebraicClosure ℚ)) h
  ·
    ext x
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨(inclK A K a).2, (a : ↥K).2⟩
    · rintro ⟨hxA, hxK⟩
      exact ⟨⟨⟨x, hxK⟩, hxA⟩, rfl⟩
  ·
    intro ρ
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective ρ
    obtain ⟨c, hcA, hsub, hm⟩ := exists_sub_mem A q hA hresT (a : AlgebraicClosure ℚ) a.2
    have hcK : (c : AlgebraicClosure ℚ) ∈ K := IntermediateField.algebraMap_mem K c
    refine ⟨⟨⟨(c : AlgebraicClosure ℚ), hcK⟩, hcA⟩, ?_⟩
    have hsub' : a - inclK A K ⟨⟨(c : AlgebraicClosure ℚ), hcK⟩, hcA⟩ =
        ⟨(a : AlgebraicClosure ℚ) - c, hsub⟩ := Subtype.ext rfl
    rw [← hsub', ← Ideal.Quotient.mk_eq_mk_iff_sub_mem] at hm
    exact hm.symm
  ·
    apply le_antisymm
    · intro x hx
      rw [Ideal.mem_span_singleton']
      by_cases hx0 : x = 0
      · exact ⟨0, by rw [hx0, zero_mul]⟩
      have hxQ0 : ((x : ↥K) : AlgebraicClosure ℚ) ≠ 0 := by
        intro h
        apply hx0
        apply Subtype.ext
        apply Subtype.ext
        simpa using h
      obtain ⟨m, hm⟩ :=
        exists_valuation_eq_zpow_layer A q hA hdvrT hirrT π hπ ((x : ↥K) : AlgebraicClosure ℚ) (x : ↥K).2 hxQ0

      have hxA : inclK A K x ∈ maximalIdeal ↥A := by
        rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hx ⊢
        exact fun hu => hx ((isUnit_map_iff (inclK A K) x).mp hu)
      have hvx : A.valuation ((x : ↥K) : AlgebraicClosure ℚ) < 1 := (A.valuation_lt_one_iff _).mp hxA
      have hm1 : 1 ≤ m := by
        by_contra hlt
        push Not at hlt
        have : 1 ≤ A.valuation π ^ m := one_le_zpow_of_nonpos₀ hvπ0 hvπ1.le (by omega)
        rw [← hm] at this
        exact absurd hvx (not_lt.mpr this)

      let y : AlgebraicClosure ℚ := ((x : ↥K) : AlgebraicClosure ℚ) * π⁻¹
      have hvy : A.valuation y ≤ 1 := by
        have : A.valuation y = A.valuation π ^ (m - 1) := by
          rw [zpow_sub_one₀ hvπ0.ne', ← hm, ← map_inv₀, ← map_mul]
        rw [this]
        exact zpow_le_one₀ hvπ0 hvπ1.le (by omega)
      have hyA : y ∈ A := (A.valuation_le_one_iff y).mp hvy
      have hyK : y ∈ K := mul_mem (x : ↥K).2 (inv_mem hπK)
      refine ⟨⟨⟨y, hyK⟩, hyA⟩, ?_⟩
      apply Subtype.ext
      apply Subtype.ext
      show y * π = ((x : ↥K) : AlgebraicClosure ℚ)
      simp only [y]
      rw [mul_assoc, inv_mul_cancel₀ hπ0, mul_one]
    · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, IsLocalRing.mem_maximalIdeal,
        mem_nonunits_iff]
      intro hu
      obtain ⟨u, hu'⟩ := hu.map (inclK A K)
      have h1 : A.valuation π = 1 := by
        have := A.valuation_unit u
        rw [hu'] at this
        exact this
      exact hvπ1.ne h1

end S_ValuationSubring_exists_subfield_henselian_isDiscreteValuationRing_inf_of_liesOverPrime
end P2MW
export P2MW.S_ValuationSubring_exists_subfield_henselian_isDiscreteValuationRing_inf_of_liesOverPrime (solution)
