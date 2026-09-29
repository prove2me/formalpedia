-- Prove2me | solution 1 for ValuationSubring.exists_dvr_subring_of_forall_mem_inertiaSubgroupIn
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/4c0af733-cc54-5963-9e70-133c5243468f

import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import Theorems.Thm_ValuationSubring_exists_ideal_ringOfIntegers_inertia_eq_map_restrictNormalHom
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_exists_dvr_subring_of_forall_mem_inertiaSubgroupIn

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 800000

namespace G3

local notation "Qb" => AlgebraicClosure ℚ

open scoped Pointwise

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

theorem mem_of_isIntegral_int {Kf : Type*} [Field Kf] (A : ValuationSubring Kf) {r : Kf} (hr : IsIntegral ℤ r) : r ∈ A := by
  obtain ⟨p, hpm, hp⟩ := hr
  by_contra hrV
  have hr0 : r ≠ 0 := by rintro rfl; exact hrV A.zero_mem
  have hy : A.valuation r⁻¹ < 1 := by
    have hx : ¬ A.valuation r ≤ 1 := by rwa [A.valuation_le_one_iff]
    rw [map_inv₀]; push_neg at hx
    exact inv_lt_one_of_one_lt₀ hx
  set n := p.natDegree
  have heval : r ^ n + ∑ i ∈ Finset.range n, algebraMap ℤ Kf (p.coeff i) * r ^ i = 0 := by
    have : Polynomial.eval₂ (algebraMap ℤ Kf) r p = 0 := hp
    rw [Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ] at this
    simp only [Polynomial.coeff_natDegree, hpm.leadingCoeff, map_one, one_mul] at this
    rw [add_comm] at this; exact this
  have key : (1 : Kf) = - ∑ i ∈ Finset.range n, algebraMap ℤ Kf (p.coeff i) * r⁻¹ ^ (n - i) := by
    have h2 : ∑ i ∈ Finset.range n, algebraMap ℤ Kf (p.coeff i) * r⁻¹ ^ (n - i)
        = (∑ i ∈ Finset.range n, algebraMap ℤ Kf (p.coeff i) * r ^ i) * r⁻¹ ^ n := by
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
  have hlt : A.valuation (∑ i ∈ Finset.range n, algebraMap ℤ Kf (p.coeff i) * r⁻¹ ^ (n - i)) < 1 := by
    refine Valuation.map_sum_lt _ one_ne_zero fun i hi => ?_
    have hi' : 1 ≤ n - i := by have := Finset.mem_range.mp hi; omega
    rw [map_mul, map_pow]
    calc A.valuation (algebraMap ℤ Kf (p.coeff i)) * A.valuation r⁻¹ ^ (n - i)
        ≤ 1 * A.valuation r⁻¹ ^ (n - i) := by
          gcongr
          exact (A.valuation_le_one_iff _).mpr (by simpa using intCast_mem A.toSubring (p.coeff i))
      _ < 1 := by rw [one_mul]; exact pow_lt_one₀ zero_le' hy (by omega)
  have : A.valuation (1 : Kf) < 1 := by rw [key, Valuation.map_neg]; exact hlt
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

theorem valuation_comap_lt_one_iff {K L : Type*} [Field K] [Field L] (f : K →+* L) (A : ValuationSubring L) (x : K) :
    (A.comap f).valuation x < 1 ↔ A.valuation (f x) < 1 := by
  rw [← ValuationSubring.mem_nonunits_iff, ← ValuationSubring.mem_nonunits_iff,
    mem_nonunits_iff_eq_zero_or_inv_not_mem, mem_nonunits_iff_eq_zero_or_inv_not_mem,
    ValuationSubring.mem_comap, map_inv₀, map_eq_zero_iff f f.injective]

theorem c561601a_served
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ F] [IsGalois ℚ F]
    (P : ValuationSubring (AlgebraicClosure ℚ)) {q : ℕ} (hq : q.Prime) (hP : P.LiesOverPrime q) :
    ∃ Q : Ideal (NumberField.RingOfIntegers F), Q.IsMaximal ∧ Finite (NumberField.RingOfIntegers F ⧸ Q) ∧
      (q : NumberField.RingOfIntegers F) ∈ Q ∧
      (∀ x : NumberField.RingOfIntegers F, P.valuation (algebraMap F (AlgebraicClosure ℚ) x) ≤ 1) ∧
      (∀ x : NumberField.RingOfIntegers F, x ∈ Q ↔ P.valuation (algebraMap F (AlgebraicClosure ℚ) x) < 1) ∧
      (P.inertiaSubgroupIn ℚ).map (AlgEquiv.restrictNormalHom F) = Q.inertia (F ≃ₐ[ℚ] F) ∧
      (∀ τ : F ≃ₐ[ℚ] F, τ ∈ Q.inertia (F ≃ₐ[ℚ] F) →
        (∀ x : NumberField.RingOfIntegers F, τ • x - x ∈ Q ^ 2) → ∃ a : ℕ, orderOf τ = q ^ a) ∧
      (∃ ϖ : NumberField.RingOfIntegers F, ϖ ∈ Q ∧
        (∀ x ∈ Q, ∃ y : NumberField.RingOfIntegers F, x - ϖ * y ∈ Q ^ 2) ∧
        (∀ c : NumberField.RingOfIntegers F, c * ϖ ∈ Q ^ 2 → c ∈ Q)) :=
  ValuationSubring.exists_ideal_ringOfIntegers_inertia_eq_map_restrictNormalHom F P hq hP

open NumberField IsDedekindDomain in
set_option maxHeartbeats 6400000 in

theorem B3_inertia (N : IntermediateField ℚ Qb) [FiniteDimensional ℚ N] [IsGalois ℚ N]
    (V : ValuationSubring N) (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ((ℓ : ℕ) : N) ∈ V.nonunits)
    (Q : Ideal (𝓞 N)) [hQmax : Q.IsMaximal] (hℓQ : ((ℓ : ℕ) : 𝓞 N) ∈ Q)
    (hQV : ∀ x : 𝓞 N, x ∈ Q ↔ V.valuation (x : N) < 1)
    (E : IntermediateField ℚ N) (hE : ∀ τ ∈ Q.inertia (N ≃ₐ[ℚ] N), ∀ x ∈ E, τ x = x) :
    Irreducible ((ℓ : ℕ) : V.comap (algebraMap E N)) := by
  classical
  haveI : NumberField N := by
    refine @NumberField.mk N _ inferInstance ?_
    have h : FiniteDimensional ℚ N := inferInstance
    convert h

  have hℓprime : Prime (ℓ : ℤ) := Nat.prime_iff_prime_int.mp Fact.out
  set p : Ideal ℤ := Ideal.span {(ℓ : ℤ)} with hp
  have hp0 : p ≠ ⊥ := by
    rw [hp, ne_eq, Ideal.span_singleton_eq_bot]
    exact hℓprime.ne_zero
  haveI hpmax : p.IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hℓprime.irreducible
  haveI hQp : Q.LiesOver p := by
    refine ⟨(hpmax.eq_of_le (Ideal.IsPrime.under ℤ Q).ne_top ?_)⟩
    rw [hp, Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.under_def, Ideal.mem_comap,
      eq_intCast, Int.cast_natCast]
    exact hℓQ

  set 𝔮 : Ideal (𝓞 E) := Q.under (𝓞 E) with h𝔮
  haveI hQ𝔮 : Q.LiesOver 𝔮 := ⟨rfl⟩
  haveI h𝔮max : 𝔮.IsMaximal := Ideal.IsMaximal.under (𝓞 E) Q
  have hℓ𝔮 : ((ℓ : ℕ) : 𝓞 E) ∈ 𝔮 := by
    rw [h𝔮, Ideal.under_def, Ideal.mem_comap, map_natCast]
    exact hℓQ
  have h𝔮0 : 𝔮 ≠ ⊥ := by
    intro h0
    rw [h0, Ideal.mem_bot] at hℓ𝔮
    exact (Fact.out : ℓ.Prime).ne_zero (by exact_mod_cast hℓ𝔮)

  letI : Field (ℤ ⧸ p) := Ideal.Quotient.field p
  letI : Field (𝓞 N ⧸ Q) := Ideal.Quotient.field Q
  letI : Field (𝓞 E ⧸ 𝔮) := Ideal.Quotient.field 𝔮
  haveI : Algebra.IsSeparable (ℤ ⧸ p) (𝓞 N ⧸ Q) := inferInstance
  haveI : Algebra.IsSeparable (𝓞 E ⧸ 𝔮) (𝓞 N ⧸ Q) := inferInstance

  have e1 : Nat.card (Q.inertia (N ≃ₐ[ℚ] N)) = p.ramificationIdx' Q := by
    rw [Ideal.card_inertia_eq_ramificationIdxIn p Q, Ideal.ramificationIdxIn_eq_ramificationIdx p Q (N ≃ₐ[ℚ] N),
      ← Ideal.ramificationIdx'_eq_ramificationIdx p Q hp0]

  have e2 : Nat.card (Q.inertia (N ≃ₐ[E] N)) = 𝔮.ramificationIdx' Q := by
    rw [Ideal.card_inertia_eq_ramificationIdxIn 𝔮 Q, Ideal.ramificationIdxIn_eq_ramificationIdx 𝔮 Q (N ≃ₐ[E] N),
      ← Ideal.ramificationIdx'_eq_ramificationIdx 𝔮 Q h𝔮0]
  have hcard : Nat.card (Q.inertia (N ≃ₐ[E] N)) = Nat.card (Q.inertia (N ≃ₐ[ℚ] N)) := by
    refine Nat.card_congr (Equiv.ofBijective
      (fun σ => ⟨(σ.1).restrictScalars ℚ, fun x => by
        have h := σ.2 x
        have e : ((σ.1).restrictScalars ℚ) • x = σ.1 • x := Subtype.ext rfl
        rw [e]; exact h⟩) ⟨?_, ?_⟩)
    · rintro ⟨σ, hσ⟩ ⟨σ', hσ'⟩ h
      have h' : σ.restrictScalars ℚ = σ'.restrictScalars ℚ := congrArg Subtype.val h
      exact Subtype.ext (AlgEquiv.restrictScalars_injective ℚ h')
    · rintro ⟨τ, hτ⟩
      let τ' : N ≃ₐ[E] N := { τ with commutes' := fun e => hE τ hτ e e.2 }
      refine ⟨⟨τ', fun x => ?_⟩, rfl⟩
      have h := hτ x
      have e : τ' • x = τ • x := Subtype.ext rfl
      rw [e]; exact h

  have hinjEN : Function.Injective (algebraMap (𝓞 E) (𝓞 N)) := by
    intro a b hab
    apply Subtype.ext
    apply (algebraMap E N).injective
    have := congrArg (fun z : 𝓞 N => (z : N)) hab
    exact this
  have hmap𝔮 : Ideal.map (algebraMap (𝓞 E) (𝓞 N)) 𝔮 ≠ ⊥ :=
    fun h => h𝔮0 ((Ideal.map_eq_bot_iff_of_injective hinjEN).mp h)
  have hmapp : Ideal.map (algebraMap ℤ (𝓞 N)) p ≠ ⊥ :=
    fun h => hp0 ((Ideal.map_eq_bot_iff_of_injective (algebraMap ℤ (𝓞 N)).injective_int).mp h)
  have htower : p.ramificationIdx' Q = p.ramificationIdx' 𝔮 * 𝔮.ramificationIdx' Q :=
    Ideal.ramificationIdx_algebra_tower hmap𝔮 hmapp (Ideal.map_le_iff_le_comap.mpr (le_of_eq hQ𝔮.over))
  have hpos : 0 < Nat.card (Q.inertia (N ≃ₐ[ℚ] N)) := Nat.card_pos
  have he1 : p.ramificationIdx' 𝔮 = 1 := by
    have h := htower
    rw [← e1, ← e2, hcard] at h

    have : p.ramificationIdx' 𝔮 * Nat.card (Q.inertia (N ≃ₐ[ℚ] N)) = 1 * Nat.card (Q.inertia (N ≃ₐ[ℚ] N)) := by
      rw [one_mul]; exact h.symm
    exact Nat.eq_of_mul_eq_mul_right hpos this

  set W : ValuationSubring E := V.comap (algebraMap E N) with hW

  have hRW : ∀ r : 𝓞 E, algebraMap (𝓞 E) E r ∈ W := by
    intro r
    rw [ValuationSubring.mem_comap]
    apply mem_of_isIntegral_int
    exact (RingOfIntegers.isIntegral_coe r).map_of_comp_eq (RingHom.id ℤ) (algebraMap E N) (Subsingleton.elim _ _)
  have hℓW : ((ℓ : ℕ) : E) ∈ W := by
    rw [ValuationSubring.mem_comap, map_natCast]; exact V.nonunits_subset hℓ
  have hℓWinv : ((ℓ : ℕ) : E)⁻¹ ∉ W := by
    rw [ValuationSubring.mem_comap, map_inv₀, map_natCast]
    exact ((mem_nonunits_iff_eq_zero_or_inv_not_mem V _).mp hℓ).resolve_left
      (by exact_mod_cast (Fact.out : ℓ.Prime).ne_zero)
  have hWtop : W ≠ ⊤ := fun h => hℓWinv (by rw [h]; exact ValuationSubring.mem_top _)
  obtain ⟨v, hWv, hv⟩ := B1 W hRW hWtop

  have hv𝔮 : v.asIdeal = 𝔮 := by
    ext r
    rw [hv r, h𝔮, Ideal.under_def, Ideal.mem_comap, hQV, ValuationSubring.mem_nonunits_iff, hW,
      valuation_comap_lt_one_iff]
    exact Iff.rfl

  have hvℓ_lt : v.intValuation ((ℓ : ℕ) : 𝓞 E) < 1 := by
    rw [HeightOneSpectrum.intValuation_lt_one_iff_mem, hv𝔮]; exact hℓ𝔮
  have hvℓ_not_le : ¬ v.intValuation ((ℓ : ℕ) : 𝓞 E) ≤ WithZero.exp (-(2 : ℤ)) := by
    intro hle
    have hdvd : v.asIdeal ^ 2 ∣ Ideal.span {((ℓ : ℕ) : 𝓞 E)} :=
      (HeightOneSpectrum.intValuation_le_pow_iff_dvd v _ 2).mp (by exact_mod_cast hle)
    have hspan : Ideal.map (algebraMap ℤ (𝓞 E)) p = Ideal.span {((ℓ : ℕ) : 𝓞 E)} := by
      rw [hp, Ideal.map_span, Set.image_singleton, eq_intCast, Int.cast_natCast]
    have hmapp' : Ideal.map (algebraMap ℤ (𝓞 E)) p ≠ ⊥ := by
      rw [hspan, ne_eq, Ideal.span_singleton_eq_bot]
      exact_mod_cast (Fact.out : ℓ.Prime).ne_zero
    have hcount : p.ramificationIdx' 𝔮 = Multiset.count 𝔮 (UniqueFactorizationMonoid.normalizedFactors
        (Ideal.map (algebraMap ℤ (𝓞 E)) p)) :=
      Ideal.IsDedekindDomain.ramificationIdx'_eq_normalizedFactors_count hmapp' h𝔮max.isPrime h𝔮0
    rw [hv𝔮, ← hspan] at hdvd
    have h2 : (2 : ℕ∞) ≤ emultiplicity 𝔮 (Ideal.map (algebraMap ℤ (𝓞 E)) p) :=
      (pow_dvd_iff_le_emultiplicity).mp hdvd
    rw [UniqueFactorizationMonoid.emultiplicity_eq_count_normalizedFactors
        ((Ideal.prime_of_isPrime h𝔮0 h𝔮max.isPrime).irreducible) hmapp', normalize_eq, ← hcount, he1] at h2
    norm_num at h2
  have hvℓ : v.intValuation ((ℓ : ℕ) : 𝓞 E) = WithZero.exp (-(1 : ℤ)) := by
    have hne : v.intValuation ((ℓ : ℕ) : 𝓞 E) ≠ 0 := by
      rw [HeightOneSpectrum.intValuation_def, if_neg (by exact_mod_cast (Fact.out : ℓ.Prime).ne_zero)]
      exact WithZero.coe_ne_zero
    obtain ⟨m, hm⟩ : ∃ m : ℤ, v.intValuation ((ℓ : ℕ) : 𝓞 E) = WithZero.exp m :=
      ⟨Multiplicative.toAdd (WithZero.unzero hne), (WithZero.coe_unzero hne).symm⟩
    rw [hm] at hvℓ_lt hvℓ_not_le ⊢
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at hvℓ_lt
    rw [WithZero.exp_le_exp, not_le] at hvℓ_not_le
    congr 1
    omega

  have hval1 : ∀ s : 𝓞 E, s ∈ v.asIdeal.primeCompl → v.valuation E (algebraMap (𝓞 E) E s) = 1 := by
    intro s hs
    rw [HeightOneSpectrum.valuation_of_algebraMap]
    exact le_antisymm (HeightOneSpectrum.intValuation_le_one v s)
      (not_lt.mp (fun h => hs ((HeightOneSpectrum.intValuation_lt_one_iff_mem v s).mp h)))
  have hWmem_to : ∀ x : E, x ∈ W → v.valuation E x ≤ 1 := by
    intro x hx
    have hx' : x ∈ W.toSubring := hx
    rw [hWv, HeightOneSpectrum.valuationSubringAtPrime_toSubring, Subalgebra.mem_toSubring] at hx'
    have hx'' : ∃ a s : 𝓞 E, ∃ _ : s ∈ v.asIdeal.primeCompl,
        x = algebraMap (𝓞 E) E a * (algebraMap (𝓞 E) E s)⁻¹ := hx'
    obtain ⟨a, s, hs, rfl⟩ := hx''
    rw [map_mul, map_inv₀, hval1 s hs, inv_one, mul_one, HeightOneSpectrum.valuation_of_algebraMap]
    exact HeightOneSpectrum.intValuation_le_one v a
  have hWmem_of : ∀ x : E, v.valuation E x ≤ 1 → x ∈ W := by
    intro x hx
    rcases W.mem_or_inv_mem x with h | h
    · exact h
    rcases eq_or_ne x 0 with rfl | hx0
    · exact W.zero_mem

    have hx' : x⁻¹ ∈ W.toSubring := h
    rw [hWv, HeightOneSpectrum.valuationSubringAtPrime_toSubring, Subalgebra.mem_toSubring] at hx'
    have hx'' : ∃ a s : 𝓞 E, ∃ _ : s ∈ v.asIdeal.primeCompl,
        x⁻¹ = algebraMap (𝓞 E) E a * (algebraMap (𝓞 E) E s)⁻¹ := hx'
    obtain ⟨a, s, hs, hxas⟩ := hx''
    have hva : v.valuation E (algebraMap (𝓞 E) E a) = 1 := by
      have h1 := congrArg (v.valuation E) hxas
      rw [map_inv₀, map_mul, map_inv₀, hval1 s hs, inv_one, mul_one] at h1

      apply le_antisymm
      · rw [HeightOneSpectrum.valuation_of_algebraMap]; exact HeightOneSpectrum.intValuation_le_one v a
      · rw [← h1]
        exact one_le_inv_iff₀.mpr ⟨(Valuation.pos_iff _).mpr hx0, hx⟩
    have ha : a ∈ v.asIdeal.primeCompl := by
      intro ha
      have := (HeightOneSpectrum.intValuation_lt_one_iff_mem v a).mpr ha
      rw [← HeightOneSpectrum.valuation_of_algebraMap (K := E), hva] at this
      exact lt_irrefl _ this
    have hs0 : algebraMap (𝓞 E) E s ≠ 0 := by
      intro h0; have := hval1 s hs; rw [h0, map_zero] at this; exact zero_ne_one this
    have hxsa : x = algebraMap (𝓞 E) E s * (algebraMap (𝓞 E) E a)⁻¹ := by
      have := congrArg (·⁻¹) hxas
      simp only [inv_inv, mul_inv_rev] at this
      rw [this, mul_comm]
    have hmem : x ∈ (HeightOneSpectrum.valuationSubringAtPrime E v).toSubring := by
      rw [HeightOneSpectrum.valuationSubringAtPrime_toSubring, Subalgebra.mem_toSubring]
      exact ⟨s, a, ha, hxsa⟩
    rw [hWv]
    exact hmem
  have hWmem : ∀ x : E, x ∈ W ↔ v.valuation E x ≤ 1 := fun x => ⟨hWmem_to x, hWmem_of x⟩
  have hℓE : v.valuation E ((ℓ : ℕ) : E) = WithZero.exp (-(1 : ℤ)) := by
    rw [show ((ℓ : ℕ) : E) = algebraMap (𝓞 E) E ((ℓ : ℕ) : 𝓞 E) by rw [map_natCast],
      HeightOneSpectrum.valuation_of_algebraMap, hvℓ]
  have hℓE0 : ((ℓ : ℕ) : E) ≠ 0 := by exact_mod_cast (Fact.out : ℓ.Prime).ne_zero

  have hmax : IsLocalRing.maximalIdeal W = Ideal.span {(⟨((ℓ : ℕ) : E), hℓW⟩ : W)} := by
    apply le_antisymm
    · intro x hx

      have hxW : v.valuation E (x : E) ≤ 1 := (hWmem _).mp x.2
      have hxlt : v.valuation E (x : E) < 1 := by
        by_contra hge
        have hx1 : v.valuation E (x : E) = 1 := le_antisymm hxW (not_lt.mp hge)
        apply (IsLocalRing.mem_maximalIdeal _).mp hx
        have hx0 : (x : E) ≠ 0 := by
          intro h0; rw [h0, map_zero] at hx1; exact zero_ne_one hx1
        have hinv : (x : E)⁻¹ ∈ W := by rw [hWmem, map_inv₀, hx1, inv_one]
        exact IsUnit.of_mul_eq_one (⟨(x : E)⁻¹, hinv⟩ : W) (Subtype.ext (mul_inv_cancel₀ hx0))
      rcases eq_or_ne x 0 with rfl | hx0
      · exact Ideal.zero_mem _
      have hx0' : (x : E) ≠ 0 := fun h => hx0 (Subtype.ext h)
      have hxle : v.valuation E (x : E) ≤ WithZero.exp (-(1 : ℤ)) := by
        have hne : v.valuation E (x : E) ≠ 0 := (Valuation.ne_zero_iff _).mpr hx0'
        obtain ⟨m, hm⟩ : ∃ m : ℤ, v.valuation E (x : E) = WithZero.exp m :=
          ⟨Multiplicative.toAdd (WithZero.unzero hne), (WithZero.coe_unzero hne).symm⟩
        rw [hm] at hxlt ⊢
        rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at hxlt
        rw [WithZero.exp_le_exp]
        omega
      have hyW : (x : E) * ((ℓ : ℕ) : E)⁻¹ ∈ W := by
        rw [hWmem, map_mul, map_inv₀, hℓE]
        calc v.valuation E (x : E) * (WithZero.exp (-(1 : ℤ)))⁻¹
            ≤ WithZero.exp (-(1 : ℤ)) * (WithZero.exp (-(1 : ℤ)))⁻¹ := by gcongr
          _ = 1 := mul_inv_cancel₀ WithZero.coe_ne_zero
      rw [Ideal.mem_span_singleton']
      refine ⟨⟨_, hyW⟩, Subtype.ext ?_⟩
      show (x : E) * ((ℓ : ℕ) : E)⁻¹ * ((ℓ : ℕ) : E) = x
      rw [inv_mul_cancel_right₀ hℓE0]
    · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      rintro ⟨u, hu⟩
      apply hℓWinv
      have h1 : ((u : W) : E) * (((u⁻¹ : Wˣ) : W) : E) = 1 := by
        rw [← MulMemClass.coe_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, OneMemClass.coe_one]
      have h2 : ((u : W) : E) = ((ℓ : ℕ) : E) := by rw [hu]
      rw [h2] at h1
      rw [← eq_inv_of_mul_eq_one_right h1]
      exact ((u⁻¹ : Wˣ) : W).2
  have hℓcoe : ((ℓ : ℕ) : W) = ⟨((ℓ : ℕ) : E), hℓW⟩ := Subtype.ext (by simp)

  haveI : IsDiscreteValuationRing W := by
    have hnf : ¬ IsField W := by
      intro hf
      have hℓ0 : (⟨((ℓ : ℕ) : E), hℓW⟩ : W) ≠ 0 := fun h0 => hℓE0 (congrArg Subtype.val h0)
      obtain ⟨y, hy⟩ := hf.mul_inv_cancel hℓ0
      apply hℓWinv
      have hy' : ((ℓ : ℕ) : E) * (y : E) = 1 := by
        have := congrArg Subtype.val hy
        simpa using this
      rw [← eq_inv_of_mul_eq_one_right hy']
      exact y.2
    have hdd : IsDedekindDomain W := by rw [hWv]; infer_instance
    exact ((IsDiscreteValuationRing.TFAE W hnf).out 0 2).mpr hdd
  rw [hℓcoe, IsDiscreteValuationRing.irreducible_iff_uniformizer]
  exact hmax

variable (F : IntermediateField ℚ Qb) [FiniteDimensional ℚ F]

set_option maxHeartbeats 6400000 in

theorem irreducible_natCast_comap_inertia (ℓ : ℕ) [Fact ℓ.Prime] (A : ValuationSubring Qb)
    (hA : ((ℓ : ℕ) : Qb) ∈ A.nonunits)
    (hfix : ∀ x : F, ∀ σ : Qb ≃ₐ[ℚ] Qb, σ ∈ A.inertiaSubgroupIn ℚ → σ (x : Qb) = x) :
    Irreducible ((ℓ : ℕ) : A.comap (algebraMap F Qb)) := by
  classical
  let N : IntermediateField ℚ Qb := IntermediateField.normalClosure ℚ F Qb
  have hFN : F ≤ N := IntermediateField.le_normalClosure F
  haveI hfdN : FiniteDimensional ℚ N := normalClosure.is_finiteDimensional ℚ F Qb
  haveI hnormN : Normal ℚ N := normalClosure.normal ℚ F Qb
  haveI hgalN : IsGalois ℚ N := IsGalois.normalClosure ℚ F Qb

  let V : ValuationSubring N := A.comap (algebraMap N Qb)
  have hℓV : ((ℓ : ℕ) : N) ∈ V.nonunits := by
    rw [mem_nonunits_iff_eq_zero_or_inv_not_mem]
    right
    rw [ValuationSubring.mem_comap, map_inv₀, map_natCast]
    exact ((mem_nonunits_iff_eq_zero_or_inv_not_mem A _).mp hA).resolve_left
      (by exact_mod_cast (Fact.out : ℓ.Prime).ne_zero)

  obtain ⟨Q, hQmax, -, hℓQ, -, hQval, hIeq, -, -⟩ := c561601a_served N A (Fact.out : ℓ.Prime) hA
  haveI := hQmax
  have hQV : ∀ x : NumberField.RingOfIntegers N, x ∈ Q ↔ V.valuation (x : N) < 1 := by
    intro x
    rw [hQval x, show V = A.comap (algebraMap N Qb) from rfl, valuation_comap_lt_one_iff]

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

  have hE : ∀ τ ∈ Q.inertia (N ≃ₐ[ℚ] N), ∀ x ∈ E, τ x = x := by
    intro τ hτ x hx
    rw [← hIeq] at hτ
    obtain ⟨σ, hσI, rfl⟩ := Subgroup.mem_map.mp hτ
    apply (algebraMap N Qb).injective
    rw [show AlgEquiv.restrictNormalHom N σ = σ.restrictNormal N from rfl, AlgEquiv.restrictNormal_commutes]
    exact hfix ⟨(x : Qb), hx⟩ σ hσI
  have hℓQ' : ((ℓ : ℕ) : NumberField.RingOfIntegers N) ∈ Q := hℓQ
  have hirr := B3_inertia N V ℓ hℓV Q hℓQ' hQV E hE

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

end G3
p2m_reactivate "P2MW.S_ValuationSubring_exists_dvr_subring_of_forall_mem_inertiaSubgroupIn.G3"

open G3 in
theorem solution
    (ℓ : ℕ) [Fact ℓ.Prime] (A : ValuationSubring (AlgebraicClosure ℚ))
    (hA : ((ℓ : ℕ) : AlgebraicClosure ℚ) ∈ A.nonunits)
    (S : Finset (AlgebraicClosure ℚ))
    (hS : ∀ x ∈ S, x ∈ A ∧ ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      σ ∈ A.inertiaSubgroupIn ℚ → σ x = x) :
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
      σ ∈ A.inertiaSubgroupIn ℚ → σ (x : AlgebraicClosure ℚ) = x := by
    intro x σ hσ
    have hle : F ≤ IntermediateField.fixedField (A.inertiaSubgroupIn ℚ) := by
      rw [hF, IntermediateField.adjoin_le_iff]
      intro s hs
      rw [SetLike.mem_coe, IntermediateField.mem_fixedField_iff]
      intro g hg
      exact (hS s hs).2 g hg
    exact (IntermediateField.mem_fixedField_iff _ _).mp (hle x.2) σ hσ
  haveI hdvr : IsDiscreteValuationRing V := isDiscreteValuationRing_comap F ℓ A hA
  have hirr : Irreducible ((ℓ : ℕ) : V) := irreducible_natCast_comap_inertia F ℓ A hA hfix
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

end S_ValuationSubring_exists_dvr_subring_of_forall_mem_inertiaSubgroupIn
end P2MW
export P2MW.S_ValuationSubring_exists_dvr_subring_of_forall_mem_inertiaSubgroupIn (solution)
