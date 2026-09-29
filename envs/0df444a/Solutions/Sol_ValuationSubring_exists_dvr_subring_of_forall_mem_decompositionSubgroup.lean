-- Prove2me | solution 1 for ValuationSubring.exists_dvr_subring_of_forall_mem_decompositionSubgroup
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/f8bdcf05-e698-58fa-8634-5c65476977ed

import Mathlib
import Theorems.Thm_ValuationSubring_exists_mem_decompositionSubgroup_restrictNormal_eq
import Theorems.Thm_ValuationSubring_irreducible_natCast_comap_of_forall_smul_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_exists_dvr_subring_of_forall_mem_decompositionSubgroup

open scoped Pointwise

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 800000

namespace CTb

local notation "Qb" => AlgebraicClosure ℚ

theorem algebraMap_rat_mem_of_den_coprime (ℓ : ℕ) [Fact ℓ.Prime]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : ((ℓ : ℕ) : AlgebraicClosure ℚ) ∈ A.nonunits)
    (q : ℚ) (hq : q.den.Coprime ℓ) : algebraMap ℚ (AlgebraicClosure ℚ) q ∈ A := by
  rw [← ValuationSubring.valuation_le_one_iff]
  have hℓ : A.valuation ((ℓ : ℕ) : AlgebraicClosure ℚ) < 1 := (ValuationSubring.mem_nonunits_iff A).mp hA
  have hint : ∀ n : ℤ, A.valuation (n : AlgebraicClosure ℚ) ≤ 1 := fun n => by
    rw [ValuationSubring.valuation_le_one_iff]
    exact intCast_mem A.toSubring n
  have hnat : ∀ n : ℕ, A.valuation (n : AlgebraicClosure ℚ) ≤ 1 := fun n => by
    rw [ValuationSubring.valuation_le_one_iff]
    exact natCast_mem A.toSubring n

  have hden : A.valuation (q.den : AlgebraicClosure ℚ) = 1 := by
    apply le_antisymm (hnat q.den)
    by_contra hlt
    rw [not_le] at hlt
    have hg : Int.gcd (q.den : ℤ) (ℓ : ℤ) = 1 := by
      rw [Int.gcd_natCast_natCast]; exact hq
    have hab : (q.den : ℤ) * Int.gcdA (q.den : ℤ) (ℓ : ℤ) + (ℓ : ℤ) * Int.gcdB (q.den : ℤ) (ℓ : ℤ) = 1 := by
      have := Int.gcd_eq_gcd_ab (q.den : ℤ) (ℓ : ℤ)
      rw [hg] at this
      exact_mod_cast this.symm
    have hcast : (q.den : AlgebraicClosure ℚ) * (Int.gcdA (q.den : ℤ) (ℓ : ℤ) : AlgebraicClosure ℚ) +
        ((ℓ : ℕ) : AlgebraicClosure ℚ) * (Int.gcdB (q.den : ℤ) (ℓ : ℤ) : AlgebraicClosure ℚ) = 1 := by
      exact_mod_cast congrArg (fun z : ℤ => (z : AlgebraicClosure ℚ)) hab
    have h1 : A.valuation (1 : AlgebraicClosure ℚ) < 1 := by
      rw [← hcast]
      refine lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt ?_ ?_)
      · rw [Valuation.map_mul]
        calc A.valuation (q.den : AlgebraicClosure ℚ) * A.valuation (Int.gcdA (q.den : ℤ) (ℓ : ℤ) : AlgebraicClosure ℚ)
            ≤ A.valuation (q.den : AlgebraicClosure ℚ) * 1 := by gcongr; exact hint _
          _ < 1 := by rw [mul_one]; exact hlt
      · rw [Valuation.map_mul]
        calc A.valuation ((ℓ : ℕ) : AlgebraicClosure ℚ) * A.valuation (Int.gcdB (q.den : ℤ) (ℓ : ℤ) : AlgebraicClosure ℚ)
            ≤ A.valuation ((ℓ : ℕ) : AlgebraicClosure ℚ) * 1 := by gcongr; exact hint _
          _ < 1 := by rw [mul_one]; exact hℓ
    simp at h1
  have hq' : algebraMap ℚ (AlgebraicClosure ℚ) q = (q.num : AlgebraicClosure ℚ) / (q.den : AlgebraicClosure ℚ) := by
    rw [eq_ratCast, Rat.cast_def]
  rw [hq', map_div₀, hden, div_one]
  exact hint q.num

theorem mem_of_isIntegral_int (A : ValuationSubring Qb) {r : Qb} (hr : IsIntegral ℤ r) : r ∈ A := by
  obtain ⟨p, hpm, hp⟩ := hr
  by_contra hrV
  have hr0 : r ≠ 0 := by rintro rfl; exact hrV A.zero_mem
  have hy : A.valuation r⁻¹ < 1 := by
    have hx : ¬ A.valuation r ≤ 1 := by rwa [A.valuation_le_one_iff]
    rw [map_inv₀]; push_neg at hx
    exact inv_lt_one_of_one_lt₀ hx
  set n := p.natDegree
  have heval : r ^ n + ∑ i ∈ Finset.range n, algebraMap ℤ Qb (p.coeff i) * r ^ i = 0 := by
    have : Polynomial.eval₂ (algebraMap ℤ Qb) r p = 0 := hp
    rw [Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ] at this
    simp only [Polynomial.coeff_natDegree, hpm.leadingCoeff, map_one, one_mul] at this
    rw [add_comm] at this; exact this
  have key : (1 : Qb) = - ∑ i ∈ Finset.range n, algebraMap ℤ Qb (p.coeff i) * r⁻¹ ^ (n - i) := by
    have h2 : ∑ i ∈ Finset.range n, algebraMap ℤ Qb (p.coeff i) * r⁻¹ ^ (n - i)
        = (∑ i ∈ Finset.range n, algebraMap ℤ Qb (p.coeff i) * r ^ i) * r⁻¹ ^ n := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hi' : i ≤ n := (Finset.mem_range.mp hi).le
      rw [mul_assoc]; congr 1
      calc r⁻¹ ^ (n - i) = (r * r⁻¹) ^ i * r⁻¹ ^ (n - i) := by rw [mul_inv_cancel₀ hr0, one_pow, one_mul]
        _ = r ^ i * r⁻¹ ^ n := by rw [mul_pow, mul_assoc, ← pow_add, Nat.add_sub_cancel' hi']
    rw [h2, eq_neg_iff_add_eq_zero]
    have h3 := congrArg (· * r⁻¹ ^ n) heval
    simp only [add_mul, zero_mul] at h3
    rwa [← mul_pow, mul_inv_cancel₀ hr0, one_pow] at h3
  have hlt : A.valuation (∑ i ∈ Finset.range n, algebraMap ℤ Qb (p.coeff i) * r⁻¹ ^ (n - i)) < 1 := by
    refine Valuation.map_sum_lt _ one_ne_zero fun i hi => ?_
    have hi' : 1 ≤ n - i := by have := Finset.mem_range.mp hi; omega
    rw [map_mul, map_pow]
    calc A.valuation (algebraMap ℤ Qb (p.coeff i)) * A.valuation r⁻¹ ^ (n - i)
        ≤ 1 * A.valuation r⁻¹ ^ (n - i) := by
          gcongr
          exact (A.valuation_le_one_iff _).mpr (by simpa using intCast_mem A.toSubring (p.coeff i))
      _ < 1 := by rw [one_mul]; exact pow_lt_one₀ zero_le' hy (by omega)
  have : A.valuation (1 : Qb) < 1 := by rw [key, Valuation.map_neg]; exact hlt
  simp at this

theorem isDiscreteValuationRing_of_ringEquiv {R S : Type*} [CommRing R] [IsDomain R] [CommRing S] [IsDomain S]
    [IsDiscreteValuationRing R] (e : R ≃+* S) : IsDiscreteValuationRing S := by
  haveI : IsPrincipalIdealRing S := IsPrincipalIdealRing.of_surjective e.toRingHom e.surjective
  haveI : IsLocalRing S := IsLocalRing.of_surjective' e.toRingHom e.surjective
  refine { not_a_field' := ?_ }
  intro hbot
  have hS : IsField S := (IsLocalRing.isField_iff_maximalIdeal_eq).mpr hbot
  exact IsDiscreteValuationRing.not_isField R (MulEquiv.isField hS e.toMulEquiv)

open IsDedekindDomain in

theorem B1
    {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    (V : ValuationSubring K) (hRV : ∀ r : R, algebraMap R K r ∈ V) (hV : V ≠ ⊤) :
    ∃ v : HeightOneSpectrum R, V = v.valuationSubringAtPrime K ∧
      ∀ r : R, r ∈ v.asIdeal ↔ algebraMap R K r ∈ V.nonunits := by
  classical

  let 𝔭 : Ideal R :=
    { carrier := {r | V.valuation (algebraMap R K r) < 1}
      zero_mem' := by simp
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq, map_add] at *
        exact Valuation.map_add_lt _ ha hb
      smul_mem' := fun c r hr => by
        simp only [Set.mem_setOf_eq, smul_eq_mul, map_mul] at *
        calc V.valuation (algebraMap R K c) * V.valuation (algebraMap R K r)
            ≤ 1 * V.valuation (algebraMap R K r) := by
              gcongr; exact (V.valuation_le_one_iff _).mpr (hRV c)
          _ < 1 := by rwa [one_mul] }
  have hmem𝔭 : ∀ r : R, r ∈ 𝔭 ↔ V.valuation (algebraMap R K r) < 1 := fun r => Iff.rfl
  have h𝔭prime : 𝔭.IsPrime := by
    refine ⟨?_, ?_⟩
    · rw [Ideal.ne_top_iff_one]; simp [hmem𝔭]
    · intro a b hab
      rw [hmem𝔭, map_mul, map_mul] at hab
      by_contra hcon
      push_neg at hcon
      rw [hmem𝔭, hmem𝔭, not_lt, not_lt] at hcon
      have ha : V.valuation (algebraMap R K a) = 1 := le_antisymm ((V.valuation_le_one_iff _).mpr (hRV a)) hcon.1
      have hb : V.valuation (algebraMap R K b) = 1 := le_antisymm ((V.valuation_le_one_iff _).mpr (hRV b)) hcon.2
      rw [ha, hb, one_mul] at hab
      exact lt_irrefl _ hab
  have h𝔭bot : 𝔭 ≠ ⊥ := by
    intro hbot
    apply hV

    refine top_le_iff.mp fun x _ => ?_
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R) x
    have hbV : V.valuation (algebraMap R K b) = 1 := by
      refine le_antisymm ((V.valuation_le_one_iff _).mpr (hRV b)) (not_lt.mp fun hlt => ?_)
      have : b ∈ 𝔭 := hlt
      rw [hbot, Ideal.mem_bot] at this
      exact nonZeroDivisors.ne_zero hb this
    rw [← V.valuation_le_one_iff, map_div₀, hbV, div_one]
    exact (V.valuation_le_one_iff _).mpr (hRV a)
  let v : HeightOneSpectrum R := ⟨𝔭, h𝔭prime, h𝔭bot⟩
  refine ⟨v, ?_, fun r => ?_⟩
  ·
    set W := v.valuationSubringAtPrime K with hW
    have hWV : W ≤ V := by
      intro x hx
      have hx' : x ∈ W.toSubring := hx
      rw [hW, HeightOneSpectrum.valuationSubringAtPrime_toSubring, Subalgebra.mem_toSubring] at hx'
      have hx'' : ∃ a s : R, ∃ _ : s ∈ v.asIdeal.primeCompl, x = algebraMap R K a * (algebraMap R K s)⁻¹ := hx'
      obtain ⟨a, s, hs, rfl⟩ := hx''
      have hsV : V.valuation (algebraMap R K s) = 1 := by
        refine le_antisymm ((V.valuation_le_one_iff _).mpr (hRV s)) (not_lt.mp fun hlt => hs ?_)
        exact hlt
      rw [← V.valuation_le_one_iff, map_mul, map_inv₀, hsV, inv_one, mul_one]
      exact (V.valuation_le_one_iff _).mpr (hRV a)

    have key := ValuationSubring.ofPrime_idealOfLE W V hWV
    set Q := W.idealOfLE V hWV with hQ
    haveI : Q.IsPrime := by rw [hQ, ValuationSubring.idealOfLE]; infer_instance
    rcases eq_or_ne Q ⊥ with hQbot | hQbot
    · exfalso; apply hV
      rw [← key]
      exact (ValuationSubring.ofPrime.congr_simp W Q ⊥ hQbot).trans (ValuationSubring.ofPrime_bot W)
    · have hQmax : Q.IsMaximal := Ideal.IsPrime.isMaximal inferInstance hQbot
      have hQeq : Q = IsLocalRing.maximalIdeal W := IsLocalRing.eq_maximalIdeal hQmax
      rw [← key]
      exact (ValuationSubring.ofPrime.congr_simp W Q _ hQeq).trans (ValuationSubring.ofPrime_top W)
  · rw [ValuationSubring.mem_nonunits_iff]; exact hmem𝔭 r

section NumberFieldPart

variable (F : IntermediateField ℚ Qb) [FiniteDimensional ℚ F]

theorem isDiscreteValuationRing_comap (ℓ : ℕ) [Fact ℓ.Prime] (A : ValuationSubring Qb)
    (hA : ((ℓ : ℕ) : Qb) ∈ A.nonunits) :
    IsDiscreteValuationRing (A.comap (algebraMap F Qb)) := by
  classical
  haveI : NumberField F := NumberField.mk

  have hRV : ∀ r : NumberField.RingOfIntegers F,
      algebraMap (NumberField.RingOfIntegers F) F r ∈ A.comap (algebraMap F Qb) := by
    intro r
    rw [ValuationSubring.mem_comap]
    apply mem_of_isIntegral_int
    exact (NumberField.RingOfIntegers.isIntegral_coe r).map_of_comp_eq (RingHom.id ℤ) (algebraMap F Qb)
      (Subsingleton.elim _ _)

  have hℓV : ((ℓ : ℕ) : F) ∈ A.comap (algebraMap F Qb) := by
    rw [ValuationSubring.mem_comap, map_natCast]
    exact A.nonunits_subset hA
  have hℓinv : ((ℓ : ℕ) : F)⁻¹ ∉ A.comap (algebraMap F Qb) := by
    rw [ValuationSubring.mem_comap, map_inv₀, map_natCast, ← A.valuation_le_one_iff, map_inv₀, not_le]
    have hlt := (ValuationSubring.mem_nonunits_iff A).mp hA
    have h0 : A.valuation ((ℓ : ℕ) : Qb) ≠ 0 := by
      rw [ne_eq, map_eq_zero]; exact_mod_cast (Fact.out : ℓ.Prime).ne_zero
    exact (one_lt_inv₀ (zero_lt_iff.mpr h0)).mpr hlt
  have hV : A.comap (algebraMap F Qb) ≠ ⊤ := by
    intro htop
    apply hℓinv
    rw [htop]; exact ValuationSubring.mem_top _
  obtain ⟨v, hVW, -⟩ := B1 (A.comap (algebraMap F Qb)) hRV hV
  rw [hVW]
  set W := IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime F v with hW
  have hℓW : ((ℓ : ℕ) : F) ∈ W := by rw [← hVW]; exact hℓV
  have hℓW' : ((ℓ : ℕ) : F)⁻¹ ∉ W := by rw [← hVW]; exact hℓinv
  have hnf : ¬ IsField W := by
    intro hf
    have hℓ0 : (⟨((ℓ : ℕ) : F), hℓW⟩ : W) ≠ 0 := by
      intro h0
      have := congrArg Subtype.val h0
      simp only [ZeroMemClass.coe_zero, Nat.cast_eq_zero] at this
      exact (Fact.out : ℓ.Prime).ne_zero this
    obtain ⟨y, hy⟩ := hf.mul_inv_cancel hℓ0
    apply hℓW'
    have : ((ℓ : ℕ) : F)⁻¹ = (y : F) := by
      have hy' := congrArg Subtype.val hy
      simp only [MulMemClass.coe_mul, OneMemClass.coe_one] at hy'
      exact inv_eq_of_mul_eq_one_right hy'
    rw [this]; exact y.2
  exact ((IsDiscreteValuationRing.TFAE W hnf).out 0 2).mpr (inferInstance : IsDedekindDomain W)

end NumberFieldPart

section Glue

theorem B3_abstract (N : Type*) [Field N] [NumberField N] [IsGalois ℚ N]
    (V : ValuationSubring N) (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ((ℓ : ℕ) : N) ∈ V.nonunits)
    (E : IntermediateField ℚ N)
    (hE : ∀ τ : N ≃ₐ[ℚ] N, τ • V = V → ∀ x ∈ E, τ x = x) :
    Irreducible ((ℓ : ℕ) : V.comap (algebraMap E N)) := by
  exact ValuationSubring.irreducible_natCast_comap_of_forall_smul_eq N V ℓ hℓ E hE

scoped instance qbAlgClosure : IsAlgClosure ℚ (AlgebraicClosure ℚ) := by
  refine ⟨inferInstance, ?_⟩
  convert AlgebraicClosure.isAlgebraic ℚ
  rfl
  rfl
scoped instance qbNormal : Normal ℚ (AlgebraicClosure ℚ) := IsAlgClosure.normal ℚ _
scoped instance qbGalois : IsGalois ℚ (AlgebraicClosure ℚ) := IsAlgClosure.isGalois ℚ _

def algEquivOfRingEquiv {N : Type*} [Field N] [i : Algebra ℚ N] (e : N ≃+* N) : N ≃ₐ[ℚ] N :=
  AlgEquiv.ofRingEquiv (f := e) (fun q => by rw [eq_ratCast (algebraMap ℚ N) q, map_ratCast])

theorem mem_nonunits_iff_eq_zero_or_inv_not_mem {L : Type*} [Field L] (V : ValuationSubring L) (x : L) :
    x ∈ V.nonunits ↔ x = 0 ∨ x⁻¹ ∉ V := by
  rw [ValuationSubring.mem_nonunits_iff]
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · rw [← V.valuation_le_one_iff, map_inv₀, not_le]
    simp only [hx, false_or]
    have h0 : 0 < V.valuation x := by
      rw [zero_lt_iff]; exact (_root_.map_ne_zero V.valuation).mpr hx
    constructor
    · intro h; exact (one_lt_inv₀ h0).mpr h
    · intro h; exact (one_lt_inv₀ h0).mp h

theorem CTap_served
    {K L : Type*} [Field K] [Field L] [Algebra K L] [IsGalois K L]
    (M : IntermediateField K L) [Normal K M]
    (A : ValuationSubring L) (τ : M ≃ₐ[K] M)
    (hτ : τ • (A.comap (algebraMap M L)) = A.comap (algebraMap M L)) :
    ∃ σ : L ≃ₐ[K] L, σ ∈ A.decompositionSubgroup K ∧ σ.restrictNormal M = τ := by
  exact ValuationSubring.exists_mem_decompositionSubgroup_restrictNormal_eq M A τ hτ

variable (F : IntermediateField ℚ Qb) [FiniteDimensional ℚ F]

set_option maxHeartbeats 6400000 in

theorem irreducible_natCast_comap (ℓ : ℕ) [Fact ℓ.Prime] (A : ValuationSubring Qb)
    (hA : ((ℓ : ℕ) : Qb) ∈ A.nonunits)
    (hfix : ∀ x : F, ∀ σ : Qb ≃ₐ[ℚ] Qb, σ ∈ A.decompositionSubgroup ℚ → σ (x : Qb) = x) :
    Irreducible ((ℓ : ℕ) : A.comap (algebraMap F Qb)) := by
  classical

  let N : IntermediateField ℚ Qb := IntermediateField.normalClosure ℚ F Qb
  have hFN : F ≤ N := IntermediateField.le_normalClosure F
  have hfdN : @FiniteDimensional ℚ ↥N _ _ N.module' := normalClosure.is_finiteDimensional ℚ F Qb
  have hnormN : @Normal ℚ ↥N _ _ N.algebra' := normalClosure.normal ℚ F Qb
  have hgalN : @IsGalois ℚ _ ↥N _ N.algebra' := IsGalois.normalClosure ℚ F Qb

  have hinst : (DivisionRing.toRatAlgebra : Algebra ℚ ↥N) = N.algebra' := Subsingleton.elim _ _
  have hmod : (DivisionRing.toRatAlgebra : Algebra ℚ ↥N).toModule = N.module' := by
    rw [hinst]; with_unfolding_all rfl
  haveI : NumberField ↥N := by
    refine @NumberField.mk ↥N _ inferInstance ?_
    have h := hfdN
    rw [← hmod] at h
    exact h
  haveI : IsGalois ℚ ↥N := by
    have h := hgalN
    rw [← hinst] at h
    exact h

  let V : ValuationSubring N := A.comap (algebraMap N Qb)
  have hℓV : ((ℓ : ℕ) : N) ∈ V.nonunits := by
    rw [mem_nonunits_iff_eq_zero_or_inv_not_mem]
    right
    rw [ValuationSubring.mem_comap, map_inv₀, map_natCast]
    exact ((mem_nonunits_iff_eq_zero_or_inv_not_mem A _).mp hA).resolve_left
      (by exact_mod_cast (Fact.out : ℓ.Prime).ne_zero)

  let E : IntermediateField ℚ N :=
    { carrier := {x | (x : Qb) ∈ F}
      mul_mem' := fun {a b} ha hb => F.mul_mem ha hb
      one_mem' := F.one_mem
      add_mem' := fun {a b} ha hb => F.add_mem ha hb
      zero_mem' := F.zero_mem
      algebraMap_mem' := fun q => by
        change ((algebraMap ℚ N q : N) : Qb) ∈ F
        rw [eq_ratCast, show ((q : N) : Qb) = (q : Qb) from rfl]
        exact_mod_cast F.algebraMap_mem q
      inv_mem' := fun x hx => F.inv_mem hx }
  have hmemE : ∀ x : N, x ∈ E ↔ (x : Qb) ∈ F := fun x => Iff.rfl

  have hE : ∀ τ : N ≃ₐ[ℚ] N, τ • V = V → ∀ x ∈ E, τ x = x := by
    intro τ hτ x hx

    let τ' : @AlgEquiv ℚ ↥N ↥N _ _ _ N.algebra' N.algebra' := @algEquivOfRingEquiv ↥N _ N.algebra' τ.toRingEquiv
    have hτ'app : ∀ y : N, τ' y = τ y := fun y => rfl
    have hτ' : τ' • (A.comap (algebraMap N Qb)) = A.comap (algebraMap N Qb) := by
      have : τ' • (A.comap (algebraMap N Qb)) = τ • V := by
        ext y
        simp only [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def]
        rfl
      rw [this, hτ]
    obtain ⟨σ, hσD, hσres⟩ :=
      @CTap_served ℚ Qb _ _ _ _ N hnormN A τ' hτ'
    have h1 : σ (x : Qb) = x := hfix ⟨(x : Qb), hx⟩ σ hσD
    apply (algebraMap N Qb).injective
    rw [← hτ'app, ← hσres]
    rw [@AlgEquiv.restrictNormal_commutes]
    exact h1
  have hirr := B3_abstract N V ℓ hℓV E hE

  let toE : F → E := fun x => ⟨⟨(x : Qb), hFN x.2⟩, (show ((⟨(x : Qb), hFN x.2⟩ : N) : Qb) ∈ F from x.2)⟩
  let toF : E → F := fun y => ⟨((y : N) : Qb), y.2⟩
  let Ψ : A.comap (algebraMap F Qb) ≃+* V.comap (algebraMap E N) :=
    { toFun := fun x => ⟨toE x.1, x.2⟩
      invFun := fun y => ⟨toF y.1, y.2⟩
      left_inv := fun x => rfl
      right_inv := fun y => rfl
      map_mul' := fun x y => rfl
      map_add' := fun x y => rfl }
  have hΨ : Ψ ((ℓ : ℕ) : A.comap (algebraMap F Qb)) = ((ℓ : ℕ) : V.comap (algebraMap E N)) := map_natCast Ψ ℓ
  rw [← MulEquiv.irreducible_iff Ψ.toMulEquiv]
  change Irreducible (Ψ _)
  rw [hΨ]
  exact hirr

end Glue

end CTb
p2m_reactivate "P2MW.S_ValuationSubring_exists_dvr_subring_of_forall_mem_decompositionSubgroup.CTb"

open CTb in
theorem solution
    (ℓ : ℕ) [Fact ℓ.Prime] (A : ValuationSubring (AlgebraicClosure ℚ))
    (hA : ((ℓ : ℕ) : AlgebraicClosure ℚ) ∈ A.nonunits)
    (S : Finset (AlgebraicClosure ℚ))
    (hS : ∀ x ∈ S, x ∈ A ∧ ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      σ ∈ A.decompositionSubgroup ℚ → σ x = x) :
    ∃ O : Subring (AlgebraicClosure ℚ),
      (↑S : Set (AlgebraicClosure ℚ)) ⊆ O ∧ (O : Set (AlgebraicClosure ℚ)) ⊆ A ∧
      (∀ q : ℚ, q.den.Coprime ℓ → algebraMap ℚ (AlgebraicClosure ℚ) q ∈ O) ∧
      IsDiscreteValuationRing O ∧ Irreducible ((ℓ : ℕ) : O) ∧
      ∀ x : O, A.valuation (x : AlgebraicClosure ℚ) < 1 → ¬ IsUnit x := by
  classical

  set F : IntermediateField ℚ (AlgebraicClosure ℚ) := IntermediateField.adjoin ℚ (S : Set (AlgebraicClosure ℚ))
    with hF
  haveI : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := by
    convert AlgebraicClosure.isAlgebraic ℚ
    rfl
    rfl
  haveI : FiniteDimensional ℚ F :=
    IntermediateField.finiteDimensional_adjoin (fun x _ => (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).isIntegral)

  set V : ValuationSubring F := A.comap (algebraMap F (AlgebraicClosure ℚ)) with hV
  have hinj : Function.Injective (algebraMap F (AlgebraicClosure ℚ)) := (algebraMap F (AlgebraicClosure ℚ)).injective
  set O : Subring (AlgebraicClosure ℚ) := V.toSubring.map (algebraMap F (AlgebraicClosure ℚ)) with hO
  have hmemO : ∀ y : AlgebraicClosure ℚ, y ∈ O ↔ y ∈ F ∧ y ∈ A := by
    intro y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x.2, hx⟩
    · rintro ⟨hyF, hyA⟩
      exact ⟨⟨y, hyF⟩, hyA, rfl⟩
  let e : V ≃+* O := V.toSubring.equivMapOfInjective _ hinj
  have he : ∀ x : V, ((e x : O) : AlgebraicClosure ℚ) = algebraMap F (AlgebraicClosure ℚ) (x : F) := fun x => rfl

  have hfix : ∀ x : F, ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      σ ∈ A.decompositionSubgroup ℚ → σ (x : AlgebraicClosure ℚ) = x := by
    intro x σ hσ
    have hle : F ≤ IntermediateField.fixedField (A.decompositionSubgroup ℚ) := by
      rw [hF, IntermediateField.adjoin_le_iff]
      intro s hs
      rw [SetLike.mem_coe, IntermediateField.mem_fixedField_iff]
      intro g hg
      exact (hS s hs).2 g hg
    exact (IntermediateField.mem_fixedField_iff _ _).mp (hle x.2) σ hσ
  haveI hdvr : IsDiscreteValuationRing V := isDiscreteValuationRing_comap F ℓ A hA
  have hirr : Irreducible ((ℓ : ℕ) : V) := irreducible_natCast_comap F ℓ A hA hfix
  refine ⟨O, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro s hs
    rw [SetLike.mem_coe, hmemO]
    exact ⟨IntermediateField.subset_adjoin ℚ _ hs, (hS s hs).1⟩
  · intro y hy
    exact ((hmemO y).mp hy).2
  · intro q hq
    rw [hmemO]
    exact ⟨F.algebraMap_mem q, algebraMap_rat_mem_of_den_coprime ℓ A hA q hq⟩
  · exact isDiscreteValuationRing_of_ringEquiv e
  · have : ((ℓ : ℕ) : O) = e ((ℓ : ℕ) : V) := by simp
    rw [this]
    exact (MulEquiv.irreducible_iff e.toMulEquiv).mpr hirr
  · intro x hx hunit
    obtain ⟨u, rfl⟩ := hunit
    have hinv : ((u⁻¹ : Oˣ) : O).1 ∈ A := ((hmemO _).mp ((u⁻¹ : Oˣ) : O).2).2
    have hprod : (u : O).1 * ((u⁻¹ : Oˣ) : O).1 = 1 := by
      rw [← Subring.coe_mul, Units.mul_inv]; rfl
    have h1 : A.valuation (1 : AlgebraicClosure ℚ) < 1 := by
      rw [← hprod, map_mul]
      calc A.valuation (u : O).1 * A.valuation ((u⁻¹ : Oˣ) : O).1 ≤ A.valuation (u : O).1 * 1 := by
            gcongr; exact (A.valuation_le_one_iff _).mpr hinv
        _ < 1 := by rwa [mul_one]
    simp at h1

end S_ValuationSubring_exists_dvr_subring_of_forall_mem_decompositionSubgroup
end P2MW
export P2MW.S_ValuationSubring_exists_dvr_subring_of_forall_mem_decompositionSubgroup (solution)
