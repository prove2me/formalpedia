-- Prove2me | solution 1 for ValuationSubring.irreducible_natCast_comap_of_forall_smul_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/c35df0d8-6229-5ed8-a690-cf771454d076

import Mathlib
import Theorems.Thm_ValuationSubring_exists_eq_valuationSubringAtPrime_of_forall_algebraMap_mem
import Theorems.Thm_Ideal_ramificationIdx_and_inertiaDeg_under_eq_one_of_isGaloisGroup_stabilizer
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_irreducible_natCast_comap_of_forall_smul_eq

set_option autoImplicit false
set_option maxHeartbeats 1600000

open scoped Pointwise
open IsDedekindDomain NumberField

namespace Ws25B3

section General

variable {K L : Type*} [Field K] [Field L]

theorem mem_nonunits_comap_iff (A : ValuationSubring L) (f : K →+* L) (x : K) :
    x ∈ (A.comap f).nonunits ↔ f x ∈ A.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_nonunits_iff_or,
    ValuationSubring.mem_comap, map_inv₀, map_eq_zero]

theorem mem_nonunits_pointwise_smul_iff {G : Type*} [Group G] [MulSemiringAction G L]
    (A : ValuationSubring L) (g : G) (x : L) :
    x ∈ (g • A).nonunits ↔ g⁻¹ • x ∈ A.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_nonunits_iff_or,
    ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, smul_inv'', smul_eq_zero_iff_eq]

theorem ne_top_of_mem_nonunits (A : ValuationSubring L) {x : L} (hx : x ∈ A.nonunits)
    (hx0 : x ≠ 0) : A ≠ ⊤ := by
  rintro rfl
  rcases (ValuationSubring.mem_nonunits_iff_or _).mp hx with h | h
  · exact hx0 h
  · exact h (ValuationSubring.mem_top _)

theorem not_isUnit_iff_coe_mem_nonunits (A : ValuationSubring L) (a : A) :
    ¬ IsUnit a ↔ (a : L) ∈ A.nonunits := by
  rw [ValuationSubring.valuation_eq_one_iff, ValuationSubring.mem_nonunits_iff,
    (A.valuation_le_one a).lt_iff_ne]

theorem le_exp_neg_one_of_lt_one {x : WithZero (Multiplicative ℤ)} (hx : x < 1) :
    x ≤ WithZero.exp (-1 : ℤ) := by
  rcases eq_or_ne x 0 with h0 | h0
  · rw [h0]; exact zero_le'
  · rw [← WithZero.exp_log h0] at hx ⊢
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at hx
    rw [WithZero.exp_le_exp]
    omega

end General

section Integers

variable {N : Type*} [Field N] [NumberField N]

omit [NumberField N] in
theorem algebraMap_ringOfIntegers_mem (V : ValuationSubring N) (r : 𝓞 N) :
    algebraMap (𝓞 N) N r ∈ V := by
  have hint : IsIntegral V (algebraMap (𝓞 N) N r) := (RingOfIntegers.isIntegral_coe r).tower_top
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  rw [← hy]
  exact y.2

end Integers

section Main

variable (N : Type*) [Field N] [NumberField N] [IsGalois ℚ N]
  (V : ValuationSubring N) (ℓ : ℕ) [hprime : Fact ℓ.Prime]

theorem irreducible_natCast_comap (hℓ : ((ℓ : ℕ) : N) ∈ V.nonunits) (E : IntermediateField ℚ N)
    (hE : ∀ τ : N ≃ₐ[ℚ] N, τ • V = V → ∀ x ∈ E, τ x = x) :
    Irreducible ((ℓ : ℕ) : V.comap (algebraMap E N)) := by
  classical
  have hℓ0N : ((ℓ : ℕ) : N) ≠ 0 := by exact_mod_cast hprime.out.ne_zero

  have hRV : ∀ r : 𝓞 N, algebraMap (𝓞 N) N r ∈ V := algebraMap_ringOfIntegers_mem V
  have hVtop : V ≠ ⊤ := ne_top_of_mem_nonunits V hℓ hℓ0N
  obtain ⟨v, hVeq, hvmem⟩ :=
    ValuationSubring.exists_eq_valuationSubringAtPrime_of_forall_algebraMap_mem V hRV hVtop
  haveI hPmax : v.asIdeal.IsMaximal := v.isMaximal
  have hPbot : v.asIdeal ≠ ⊥ := v.ne_bot
  have hℓP : ((ℓ : ℕ) : 𝓞 N) ∈ v.asIdeal := (hvmem _).mpr (by rwa [map_natCast])

  have hℓ0 : (ℓ : ℤ) ≠ 0 := by exact_mod_cast hprime.out.ne_zero
  have hp : Ideal.span {(ℓ : ℤ)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]; exact hℓ0
  haveI hpmax : (Ideal.span {(ℓ : ℤ)}).IsMaximal :=
    ((Ideal.span_singleton_prime hℓ0).mpr (Nat.prime_iff_prime_int.mp hprime.out)).isMaximal hp
  haveI hover : v.asIdeal.LiesOver (Ideal.span {(ℓ : ℤ)}) := by
    refine ⟨hpmax.eq_of_le (Ideal.IsMaximal.under ℤ v.asIdeal).ne_top ?_⟩
    rw [Ideal.span_singleton_le_iff_mem, Ideal.under_def, Ideal.mem_comap, map_natCast]
    exact hℓP

  have hstab : ∀ τ : N ≃ₐ[ℚ] N, τ • v.asIdeal = v.asIdeal → τ • V = V := by
    intro τ hτ
    have hRV' : ∀ r : 𝓞 N, algebraMap (𝓞 N) N r ∈ τ • V := fun r => by
      rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
      exact hRV (τ⁻¹ • r)
    have hℓ' : ((ℓ : ℕ) : N) ∈ (τ • V).nonunits := by
      rw [mem_nonunits_pointwise_smul_iff, AlgEquiv.smul_def, map_natCast]
      exact hℓ
    obtain ⟨v', hV'eq, hv'mem⟩ :=
      ValuationSubring.exists_eq_valuationSubringAtPrime_of_forall_algebraMap_mem (τ • V) hRV'
        (ne_top_of_mem_nonunits _ hℓ' hℓ0N)
    have hvv' : v' = v := by
      refine HeightOneSpectrum.ext (Ideal.ext fun r => ?_)
      rw [hv'mem r, mem_nonunits_pointwise_smul_iff,
        show τ⁻¹ • algebraMap (𝓞 N) N r = algebraMap (𝓞 N) N (τ⁻¹ • r) from rfl, ← hvmem (τ⁻¹ • r),
        ← Ideal.mem_pointwise_smul_iff_inv_smul_mem, hτ]
    rw [hV'eq, hvv', ← hVeq]

  have hEZ : ∀ x : N, x ∈ E →
      x ∈ (FixedPoints.intermediateField (MulAction.stabilizer (N ≃ₐ[ℚ] N) v.asIdeal) :
        IntermediateField ℚ N) := by
    intro x hx
    rw [FixedPoints.mem_intermediateField_iff]
    rintro ⟨τ, hτ⟩
    rw [Subgroup.mk_smul, AlgEquiv.smul_def]
    exact hE τ (hstab τ (MulAction.mem_stabilizer_iff.mp hτ)) x hx

  obtain ⟨Z, hZ⟩ : ∃ Z : IntermediateField ℚ N,
      Z = FixedPoints.intermediateField (MulAction.stabilizer (N ≃ₐ[ℚ] N) v.asIdeal) := ⟨_, rfl⟩

  haveI : Algebra.IsSeparable (ℤ ⧸ Ideal.span {(ℓ : ℤ)}) (𝓞 N ⧸ v.asIdeal) := by
    letI := Ideal.Quotient.field (Ideal.span {(ℓ : ℤ)})
    letI := Ideal.Quotient.field v.asIdeal
    haveI : Finite (𝓞 N ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot v.asIdeal hPbot
    haveI : Algebra.IsAlgebraic (ℤ ⧸ Ideal.span {(ℓ : ℤ)}) (𝓞 N ⧸ v.asIdeal) :=
      Algebra.IsAlgebraic.of_finite _ _
    infer_instance
  haveI : IsGaloisGroup (MulAction.stabilizer (N ≃ₐ[ℚ] N) v.asIdeal) (𝓞 Z) (𝓞 N) := by
    subst hZ
    exact IsGaloisGroup.of_isFractionRing _ _ _
      (FixedPoints.intermediateField (MulAction.stabilizer (N ≃ₐ[ℚ] N) v.asIdeal) :
        IntermediateField ℚ N) N
  have hCTa := Ideal.ramificationIdx_and_inertiaDeg_under_eq_one_of_isGaloisGroup_stabilizer
    (A := ℤ) (B := 𝓞 N) (C := 𝓞 Z) (N ≃ₐ[ℚ] N) (Ideal.span {(ℓ : ℤ)}) hp v.asIdeal

  have hRW : ∀ r : 𝓞 Z, algebraMap (𝓞 Z) Z r ∈ V.comap (algebraMap Z N) := fun r => by
    rw [ValuationSubring.mem_comap, ← IsScalarTower.algebraMap_apply,
      IsScalarTower.algebraMap_apply (𝓞 Z) (𝓞 N) N]
    exact hRV _
  have hℓW : ((ℓ : ℕ) : Z) ∈ (V.comap (algebraMap Z N)).nonunits := by
    rw [mem_nonunits_comap_iff, map_natCast]; exact hℓ
  have hℓ0Zf : ((ℓ : ℕ) : Z) ≠ 0 := by exact_mod_cast hprime.out.ne_zero
  obtain ⟨u, hWeq, humem⟩ :=
    ValuationSubring.exists_eq_valuationSubringAtPrime_of_forall_algebraMap_mem
      (V.comap (algebraMap Z N)) hRW (ne_top_of_mem_nonunits _ hℓW hℓ0Zf)
  have hu : u.asIdeal = v.asIdeal.under (𝓞 Z) := by
    refine Ideal.ext fun r => ?_
    rw [humem r, mem_nonunits_comap_iff, ← IsScalarTower.algebraMap_apply,
      IsScalarTower.algebraMap_apply (𝓞 Z) (𝓞 N) N, ← hvmem, Ideal.under_def, Ideal.mem_comap]

  have he : (Ideal.span {(ℓ : ℤ)}).ramificationIdx' u.asIdeal = 1 := by rw [hu]; exact hCTa.1

  have hmap : Ideal.map (algebraMap ℤ (𝓞 Z)) (Ideal.span {(ℓ : ℤ)})
      = Ideal.span {((ℓ : ℕ) : 𝓞 Z)} := by
    rw [Ideal.map_span, Set.image_singleton, map_natCast]
  have hℓ0Z : ((ℓ : ℕ) : 𝓞 Z) ≠ 0 := by exact_mod_cast hprime.out.ne_zero
  have hspan0 : Ideal.span {((ℓ : ℕ) : 𝓞 Z)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]; exact hℓ0Z
  have hmap0 : Ideal.map (algebraMap ℤ (𝓞 Z)) (Ideal.span {(ℓ : ℤ)}) ≠ ⊥ := by
    rw [hmap]; exact hspan0
  have hvalℓ : u.intValuation ((ℓ : ℕ) : 𝓞 Z) = WithZero.exp (-1 : ℤ) := by
    rw [u.intValuation_if_neg hℓ0Z, Ideal.count_associates_factors_eq hspan0 u.isPrime u.ne_bot,
      ← hmap, ← Ideal.IsDedekindDomain.ramificationIdx'_eq_normalizedFactors_count hmap0 u.isPrime
        u.ne_bot, he, Nat.cast_one]
  have hvalℓ' : u.valuation Z ((ℓ : ℕ) : Z) = WithZero.exp (-1 : ℤ) := by
    rw [← map_natCast (algebraMap (𝓞 Z) Z) ℓ, HeightOneSpectrum.valuation_of_algebraMap, hvalℓ]

  have hcore : ∀ x : N, x ∈ Z → x ∈ V.nonunits → x * ((ℓ : ℕ) : N)⁻¹ ∈ V := by
    intro x hxZ hxV
    obtain ⟨z, rfl⟩ : ∃ z : Z, algebraMap Z N z = x := ⟨⟨x, hxZ⟩, rfl⟩
    have hzW : z ∈ (V.comap (algebraMap Z N)).nonunits := by
      rw [mem_nonunits_comap_iff]; exact hxV

    have hlt : u.valuation Z z < 1 := by
      refine lt_of_not_ge fun hge => ?_
      rcases (ValuationSubring.mem_nonunits_iff_or _).mp hzW with h0 | hinv
      · rw [h0, map_zero] at hge
        exact not_lt_of_ge hge zero_lt_one
      · apply hinv
        rw [hWeq, HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring,
          Valuation.mem_valuationSubring_iff, map_inv₀]
        exact inv_le_one_of_one_le₀ hge
    have hle : u.valuation Z z ≤ WithZero.exp (-1 : ℤ) := le_exp_neg_one_of_lt_one hlt

    have hmem : z * ((ℓ : ℕ) : Z)⁻¹ ∈ V.comap (algebraMap Z N) := by
      rw [hWeq, HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring,
        Valuation.mem_valuationSubring_iff, map_mul, map_inv₀, hvalℓ', ← WithZero.exp_neg, neg_neg]
      calc u.valuation Z z * WithZero.exp (1 : ℤ)
          ≤ WithZero.exp (-1 : ℤ) * WithZero.exp (1 : ℤ) := by gcongr
        _ = 1 := by rw [← WithZero.exp_add, neg_add_cancel, WithZero.exp_zero]
    have h := ValuationSubring.mem_comap.mp hmem
    rwa [map_mul, map_inv₀, map_natCast] at h

  refine irreducible_iff.mpr ⟨?_, ?_⟩
  · rw [not_isUnit_iff_coe_mem_nonunits,
      show (((ℓ : ℕ) : V.comap (algebraMap E N)) : E) = (ℓ : E) from
        map_natCast (V.comap (algebraMap E N)).subtype ℓ,
      mem_nonunits_comap_iff, map_natCast]
    exact hℓ
  · intro a b hab
    by_cases ha : IsUnit a
    · exact Or.inl ha
    right
    have haV : algebraMap E N a ∈ V.nonunits := by
      rwa [not_isUnit_iff_coe_mem_nonunits, mem_nonunits_comap_iff] at ha
    have haE : algebraMap E N a ∈ E := by
      rw [IntermediateField.algebraMap_apply]; exact (a : E).2
    have haZ : algebraMap E N a ∈ Z := by rw [hZ]; exact hEZ _ haE
    have hdiv := hcore _ haZ haV

    have hab' : ((ℓ : ℕ) : N) = algebraMap E N a * algebraMap E N b := by
      have h := congrArg (fun t : V.comap (algebraMap E N) =>
        algebraMap E N ((V.comap (algebraMap E N)).subtype t)) hab
      simp only [map_natCast, map_mul] at h
      exact h
    have hb0 : algebraMap E N b ≠ 0 := by
      intro h0; rw [h0, mul_zero] at hab'; exact hℓ0N hab'

    by_contra hb
    rw [not_isUnit_iff_coe_mem_nonunits, mem_nonunits_comap_iff,
      ValuationSubring.mem_nonunits_iff_or] at hb
    rcases hb with h0 | hinv
    · exact hb0 h0
    · apply hinv
      have e : (algebraMap E N b)⁻¹ = algebraMap E N a * ((ℓ : ℕ) : N)⁻¹ := by
        rw [eq_comm, mul_inv_eq_iff_eq_mul₀ hℓ0N, hab', mul_comm (algebraMap E N a),
          ← mul_assoc, inv_mul_cancel₀ hb0, one_mul]
      rw [e]
      exact hdiv

end Main

end Ws25B3

open scoped Pointwise

theorem solution (N : Type*) [Field N] [NumberField N] [IsGalois ℚ N]
    (V : ValuationSubring N) (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ((ℓ : ℕ) : N) ∈ V.nonunits)
    (E : IntermediateField ℚ N)
    (hE : ∀ τ : N ≃ₐ[ℚ] N, τ • V = V → ∀ x ∈ E, τ x = x) :
    Irreducible ((ℓ : ℕ) : V.comap (algebraMap E N)) :=
  Ws25B3.irreducible_natCast_comap N V ℓ hℓ E hE

end S_ValuationSubring_irreducible_natCast_comap_of_forall_smul_eq
end P2MW
export P2MW.S_ValuationSubring_irreducible_natCast_comap_of_forall_smul_eq (solution)
