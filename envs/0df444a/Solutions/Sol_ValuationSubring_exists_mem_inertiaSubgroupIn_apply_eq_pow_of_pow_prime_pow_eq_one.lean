-- Prove2me | solution 1 for ValuationSubring.exists_mem_inertiaSubgroupIn_apply_eq_pow_of_pow_prime_pow_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/468f7dc4-0ae5-5407-9d66-250937aaef05

import Definitions.Def_FLTPrelim_Ramification
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.NumberTheory.RamificationInertia.Unramified
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Invariant.Profinite
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.NumberTheory.Cyclotomic.Gal
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
import Mathlib.RingTheory.Polynomial.Cyclotomic.Eval
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_exists_mem_inertiaSubgroupIn_apply_eq_pow_of_pow_prime_pow_eq_one

open scoped NumberField Pointwise

noncomputable section

namespace PrimePowerInertia
namespace Seam

private scoped instance instNormal_rat : Normal ℚ (AlgebraicClosure ℚ) := by
  have h : @Normal ℚ (AlgebraicClosure ℚ) _ _ (AlgebraicClosure.instAlgebra ℚ) := inferInstance
  exact h

private scoped instance instAlgebraIsAlgebraic_rat : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := by
  have h : @Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) _ _ (AlgebraicClosure.instAlgebra ℚ) :=
    inferInstance
  exact h

private scoped instance instAlgebraIsSeparable_rat : Algebra.IsSeparable ℚ (AlgebraicClosure ℚ) := by
  have h : @Algebra.IsSeparable ℚ (AlgebraicClosure ℚ) _ _ (AlgebraicClosure.instAlgebra ℚ) :=
    inferInstance
  exact h

private scoped instance instAlgebraIsIntegral_rat : Algebra.IsIntegral ℚ (AlgebraicClosure ℚ) :=
  Algebra.isAlgebraic_iff_isIntegral.mp inferInstance

private scoped instance instIsGalois_rat : IsGalois ℚ (AlgebraicClosure ℚ) := ⟨⟩

private scoped instance instNumberField_intermediateField (L : IntermediateField ℚ (AlgebraicClosure ℚ))
    [FiniteDimensional ℚ L] : NumberField L where
  to_charZero := charZero_of_injective_algebraMap (algebraMap ℚ L).injective
  to_finiteDimensional := inferInstance

end PrimePowerInertia.Seam
p2m_reactivate "P2MW.S_ValuationSubring_exists_mem_inertiaSubgroupIn_apply_eq_pow_of_pow_prime_pow_eq_one.PrimePowerInertia P2MW.S_ValuationSubring_exists_mem_inertiaSubgroupIn_apply_eq_pow_of_pow_prime_pow_eq_one.PrimePowerInertia.Seam"
p2m_reactivate "P2MW.S_ValuationSubring_exists_mem_inertiaSubgroupIn_apply_eq_pow_of_pow_prime_pow_eq_one.PrimePowerInertia"

namespace PrimePowerInertia

open ValuationSubring

section Integers

variable (A : ValuationSubring (AlgebraicClosure ℚ))

private theorem mem_of_isIntegral_int {b : AlgebraicClosure ℚ} (hb : IsIntegral ℤ b) : b ∈ A := by
  have hbA : IsIntegral A b := by
    obtain ⟨f, hf, hfb⟩ := hb
    refine ⟨f.map (Int.castRingHom A), hf.map _, ?_⟩
    rw [Polynomial.eval₂_map,
      show (algebraMap A (AlgebraicClosure ℚ)).comp (Int.castRingHom A) =
        algebraMap ℤ (AlgebraicClosure ℚ) from RingHom.ext_int _ _]
    exact hfb
  obtain ⟨y, hy⟩ :=
    (IsIntegrallyClosed.isIntegral_iff (R := A) (K := AlgebraicClosure ℚ)).mp hbA
  rw [← hy]
  exact y.2

private theorem coe_integralClosure_mem (b : integralClosure ℤ (AlgebraicClosure ℚ)) :
    (b : AlgebraicClosure ℚ) ∈ A :=
  (mem_of_isIntegral_int A) b.2

variable (L : IntermediateField ℚ (AlgebraicClosure ℚ))

private theorem algebraMap_ringOfIntegers_mem (x : 𝓞 L) :
    algebraMap L (AlgebraicClosure ℚ) (x : L) ∈ A :=
  (mem_of_isIntegral_int A)
    (map_isIntegral_int (algebraMap L (AlgebraicClosure ℚ))
      (NumberField.RingOfIntegers.isIntegral_coe x))

private theorem valuation_algebraMap_ringOfIntegers_le_one (x : 𝓞 L) :
    A.valuation (algebraMap L (AlgebraicClosure ℚ) (x : L)) ≤ 1 :=
  (A.valuation_le_one_iff _).mpr ((algebraMap_ringOfIntegers_mem A) L x)

private def ringOfIntegersToValuationSubring : 𝓞 L →+* A :=
  ((algebraMap L (AlgebraicClosure ℚ)).comp (algebraMap (𝓞 L) L)).codRestrict A.toSubring
    (fun x => (algebraMap_ringOfIntegers_mem A) L x)

@[scoped simp] private theorem coe_ringOfIntegersToValuationSubring (x : 𝓞 L) :
    ((ringOfIntegersToValuationSubring A) L x : AlgebraicClosure ℚ) =
      algebraMap L (AlgebraicClosure ℚ) (x : L) := rfl

private def primeBelow : Ideal (𝓞 L) :=
  (IsLocalRing.maximalIdeal A).comap ((ringOfIntegersToValuationSubring A) L)

private theorem mem_primeBelow_iff {x : 𝓞 L} :
    x ∈ (primeBelow A) L ↔ A.valuation (algebraMap L (AlgebraicClosure ℚ) (x : L)) < 1 := by
  rw [primeBelow, Ideal.mem_comap, valuation_lt_one_iff]
  rfl

private theorem mem_primeBelow_iff_mem_nonunits {x : 𝓞 L} :
    x ∈ (primeBelow A) L ↔ algebraMap L (AlgebraicClosure ℚ) (x : L) ∈ A.nonunits := by
  rw [mem_primeBelow_iff, ValuationSubring.mem_nonunits_iff]

private theorem notMem_primeBelow_iff {x : 𝓞 L} :
    x ∉ (primeBelow A) L ↔ A.valuation (algebraMap L (AlgebraicClosure ℚ) (x : L)) = 1 := by
  rw [mem_primeBelow_iff, not_lt]
  exact ⟨fun h => le_antisymm ((valuation_algebraMap_ringOfIntegers_le_one A) L x) h,
    fun h => h.ge⟩

private scoped instance primeBelow_isPrime : ((primeBelow A) L).IsPrime :=
  Ideal.IsPrime.comap _

variable {p : ℕ}

private theorem natCast_mem_primeBelow (hA : A.LiesOverPrime p) : (p : 𝓞 L) ∈ (primeBelow A) L := by
  rw [mem_primeBelow_iff_mem_nonunits]
  change algebraMap L (AlgebraicClosure ℚ) (algebraMap (𝓞 L) L (p : 𝓞 L)) ∈ A.nonunits
  rw [map_natCast, map_natCast]
  exact hA

private theorem primeBelow_ne_bot (hp : p.Prime) (hA : A.LiesOverPrime p) : (primeBelow A) L ≠ ⊥ := by
  intro h
  have := (natCast_mem_primeBelow A) L hA
  rw [h, Ideal.mem_bot, Nat.cast_eq_zero] at this
  exact hp.ne_zero this

private theorem span_natCast_isMaximal (hp : p.Prime) : (Ideal.span {(p : ℤ)}).IsMaximal :=
  ((Ideal.span_singleton_prime (Int.natCast_ne_zero.mpr hp.ne_zero)).mpr
    (Nat.prime_iff_prime_int.mp hp)).isMaximal
    (by simpa [Ideal.span_singleton_eq_bot] using hp.ne_zero)

private theorem under_int_primeBelow (hp : p.Prime) (hA : A.LiesOverPrime p) :
    ((primeBelow A) L).under ℤ = Ideal.span {(p : ℤ)} := by
  refine ((span_natCast_isMaximal hp).eq_of_le (Ideal.IsPrime.under ℤ _).ne_top ?_).symm
  rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap, map_natCast]
  exact (natCast_mem_primeBelow A) L hA

private theorem primeBelow_liesOver (hp : p.Prime) (hA : A.LiesOverPrime p) :
    ((primeBelow A) L).LiesOver (Ideal.span {(p : ℤ)}) :=
  ⟨((under_int_primeBelow A) L hp hA).symm⟩

private theorem isMaximal_primeBelow [FiniteDimensional ℚ L] (hp : p.Prime) (hA : A.LiesOverPrime p) :
    ((primeBelow A) L).IsMaximal :=
  ((primeBelow_isPrime A) L).isMaximal ((primeBelow_ne_bot A) L hp hA)

end Integers
p2m_reactivate "P2MW.S_ValuationSubring_exists_mem_inertiaSubgroupIn_apply_eq_pow_of_pow_prime_pow_eq_one.PrimePowerInertia P2MW.S_ValuationSubring_exists_mem_inertiaSubgroupIn_apply_eq_pow_of_pow_prime_pow_eq_one.PrimePowerInertia.Seam"

section Localization

variable (A : ValuationSubring (AlgebraicClosure ℚ)) (L : IntermediateField ℚ (AlgebraicClosure ℚ))
  {p : ℕ}

private def heightOneSpectrumBelow (hp : p.Prime) (hA : A.LiesOverPrime p) :
    IsDedekindDomain.HeightOneSpectrum (𝓞 L) :=
  ⟨(primeBelow A) L, inferInstance, (primeBelow_ne_bot A) L hp hA⟩

@[scoped simp] private theorem heightOneSpectrumBelow_asIdeal (hp : p.Prime) (hA : A.LiesOverPrime p) :
    ((heightOneSpectrumBelow A) L hp hA).asIdeal = (primeBelow A) L := rfl

variable [FiniteDimensional ℚ L]

private theorem exists_mul_eq_of_mem (hp : p.Prime) (hA : A.LiesOverPrime p) (z : L)
    (hz : algebraMap L (AlgebraicClosure ℚ) z ∈ A) :
    ∃ x s : 𝓞 L, s ∉ (primeBelow A) L ∧ z * s = x := by
  obtain ⟨n, d, h | h⟩ :=
    ((heightOneSpectrumBelow A) L hp hA).exists_primeCompl_mul_eq_or_mul_eq (K := L) z
  · exact ⟨n, d, d.2, h⟩
  · refine ⟨d, n, ?_, h⟩

    have hd : A.valuation (algebraMap L (AlgebraicClosure ℚ) ((d : 𝓞 L) : L)) = 1 :=
      ((notMem_primeBelow_iff A) L).mp d.2
    rw [(notMem_primeBelow_iff A) L]
    refine le_antisymm ((valuation_algebraMap_ringOfIntegers_le_one A) L n) ?_
    have hzle : A.valuation (algebraMap L (AlgebraicClosure ℚ) z) ≤ 1 :=
      (A.valuation_le_one_iff _).mpr hz
    have hprod : A.valuation (algebraMap L (AlgebraicClosure ℚ) z) *
        A.valuation (algebraMap L (AlgebraicClosure ℚ) ((n : 𝓞 L) : L)) = 1 := by
      rw [← map_mul, ← map_mul]
      change A.valuation (algebraMap L (AlgebraicClosure ℚ) (z * algebraMap (𝓞 L) L n)) = 1
      rw [h]
      exact hd
    calc (1 : _) = _ := hprod.symm
      _ ≤ A.valuation (algebraMap L (AlgebraicClosure ℚ) ((n : 𝓞 L) : L)) :=
          mul_le_of_le_one_left' hzle

private theorem mem_of_adicValuation_le_one (hp : p.Prime) (hA : A.LiesOverPrime p) (z : L)
    (hz : ((heightOneSpectrumBelow A) L hp hA).valuation L z ≤ 1) :
    algebraMap L (AlgebraicClosure ℚ) z ∈ A := by
  obtain ⟨n, d, h⟩ :=
    ((heightOneSpectrumBelow A) L hp hA).exists_primeCompl_mul_eq_of_integer z hz
  have hd : A.valuation (algebraMap L (AlgebraicClosure ℚ) ((d : 𝓞 L) : L)) = 1 :=
    ((notMem_primeBelow_iff A) L).mp d.2
  have key : A.valuation (algebraMap L (AlgebraicClosure ℚ) z) *
      A.valuation (algebraMap L (AlgebraicClosure ℚ) ((d : 𝓞 L) : L)) ≤ 1 := by
    rw [← map_mul, ← map_mul]
    change A.valuation (algebraMap L (AlgebraicClosure ℚ) (z * algebraMap (𝓞 L) L d)) ≤ 1
    rw [h]
    exact (valuation_algebraMap_ringOfIntegers_le_one A) L n
  rw [hd, mul_one] at key
  exact (A.valuation_le_one_iff _).mp key

private theorem isEquiv_valuation_comap_adicValuation (hp : p.Prime) (hA : A.LiesOverPrime p) :
    (A.valuation.comap (algebraMap L (AlgebraicClosure ℚ))).IsEquiv
      (((heightOneSpectrumBelow A) L hp hA).valuation L) := by
  refine Valuation.isEquiv_iff_val_le_one.mpr fun {z} => ?_
  rw [Valuation.comap_apply, valuation_le_one_iff]
  constructor
  · intro hz
    obtain ⟨x, s, hs, hzs⟩ := (exists_mul_eq_of_mem A) L hp hA z hz
    have hs1 : ((heightOneSpectrumBelow A) L hp hA).valuation L ((s : 𝓞 L) : L) = 1 :=
      (IsDedekindDomain.HeightOneSpectrum.valuation_eq_one_iff_notMem (K := L)
        (v := (heightOneSpectrumBelow A) L hp hA)).mpr hs
    have h := congrArg (((heightOneSpectrumBelow A) L hp hA).valuation L) hzs
    rw [map_mul, hs1, mul_one] at h
    rw [h]
    exact ((heightOneSpectrumBelow A) L hp hA).valuation_le_one (K := L) x
  · exact (mem_of_adicValuation_le_one A) L hp hA z

end Localization
p2m_reactivate "P2MW.S_ValuationSubring_exists_mem_inertiaSubgroupIn_apply_eq_pow_of_pow_prime_pow_eq_one.PrimePowerInertia P2MW.S_ValuationSubring_exists_mem_inertiaSubgroupIn_apply_eq_pow_of_pow_prime_pow_eq_one.PrimePowerInertia.Seam"

section Ramification

variable (A : ValuationSubring (AlgebraicClosure ℚ)) (L : IntermediateField ℚ (AlgebraicClosure ℚ))
  [FiniteDimensional ℚ L] {p : ℕ}

omit [FiniteDimensional ℚ L] in
private theorem map_span_natCast_eq :
    Ideal.map (algebraMap ℤ (𝓞 L)) (Ideal.span {(p : ℤ)}) = Ideal.span {(p : 𝓞 L)} := by
  rw [Ideal.map_span, Set.image_singleton, map_natCast]

private theorem adicValuation_natCast_eq_exp_neg_ramificationIdx (hp : p.Prime) (hA : A.LiesOverPrime p) :
    ((heightOneSpectrumBelow A) L hp hA).valuation L (p : L) =
      WithZero.exp (-(Ideal.ramificationIdx' (Ideal.span {(p : ℤ)}) ((primeBelow A) L) : ℤ)) := by
  classical
  have hp0 : (p : 𝓞 L) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hspan0 : Ideal.span {(p : 𝓞 L)} ≠ ⊥ := by
    simpa only [ne_eq, Ideal.span_singleton_eq_bot] using hp0
  have hmap0 : Ideal.map (algebraMap ℤ (𝓞 L)) (Ideal.span {(p : ℤ)}) ≠ ⊥ := by
    rwa [map_span_natCast_eq]
  rw [show (p : L) = algebraMap (𝓞 L) L (p : 𝓞 L) from (map_natCast _ p).symm,
    IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
    IsDedekindDomain.HeightOneSpectrum.intValuation_if_neg _ hp0, heightOneSpectrumBelow_asIdeal,
    Ideal.count_associates_factors_eq hspan0 ((primeBelow_isPrime A) L)
      ((primeBelow_ne_bot A) L hp hA),
    Ideal.IsDedekindDomain.ramificationIdx'_eq_normalizedFactors_count hmap0 ((primeBelow_isPrime A) L)
      ((primeBelow_ne_bot A) L hp hA), map_span_natCast_eq]

private theorem dvd_ramificationIdx_of_valuation_pow_eq (hp : p.Prime) (hA : A.LiesOverPrime p)
    (z : L) {m a : ℕ} (hm : 0 < m) (hcop : Nat.Coprime a m)
    (hval : A.valuation (algebraMap L (AlgebraicClosure ℚ) z) ^ m =
      A.valuation (p : AlgebraicClosure ℚ) ^ a) :
    m ∣ Ideal.ramificationIdx' (Ideal.span {(p : ℤ)}) ((primeBelow A) L) := by
  set e := Ideal.ramificationIdx' (Ideal.span {(p : ℤ)}) ((primeBelow A) L) with he
  set w := ((heightOneSpectrumBelow A) L hp hA).valuation L with hw
  have hequiv := (isEquiv_valuation_comap_adicValuation A) L hp hA

  have hval' : w (z ^ m) = w ((p : L) ^ a) := by
    refine (hequiv.eq_iff).mp ?_
    simp only [Valuation.comap_apply, map_pow, map_natCast]
    exact hval
  rw [map_pow, map_pow, hw, (adicValuation_natCast_eq_exp_neg_ramificationIdx A) L hp hA,
    ← he, ← WithZero.exp_nsmul] at hval'
  have hz0 : ((heightOneSpectrumBelow A) L hp hA).valuation L z ≠ 0 := by
    intro h0
    rw [h0, zero_pow hm.ne'] at hval'
    exact WithZero.exp_ne_zero hval'.symm
  rw [← WithZero.exp_log hz0, ← WithZero.exp_nsmul, WithZero.exp_inj, nsmul_eq_mul, nsmul_eq_mul,
    mul_neg] at hval'

  have hdvd : (m : ℤ) ∣ (a : ℤ) * (e : ℤ) := by
    rw [← dvd_neg, ← hval']
    exact dvd_mul_right _ _
  have hdvd' : m ∣ a * e := by exact_mod_cast hdvd
  exact hcop.symm.dvd_of_dvd_mul_left hdvd'

end Ramification
p2m_reactivate "P2MW.S_ValuationSubring_exists_mem_inertiaSubgroupIn_apply_eq_pow_of_pow_prime_pow_eq_one.PrimePowerInertia P2MW.S_ValuationSubring_exists_mem_inertiaSubgroupIn_apply_eq_pow_of_pow_prime_pow_eq_one.PrimePowerInertia.Seam"

section General

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

private theorem valuation_sub_lt_one_of_mem_inertiaSubgroupIn' (A : ValuationSubring F) {σ : F ≃ₐ[K] F}
    (hσ : σ ∈ A.inertiaSubgroupIn K) {a : F} (ha : a ∈ A) :
    σ a ∈ A ∧ A.valuation (σ a - a) < 1 := by
  obtain ⟨d, hd, rfl⟩ := Subgroup.mem_map.mp hσ
  have hdA : (d : F ≃ₐ[K] F) • A = A := d.2
  have hmem : (d : F ≃ₐ[K] F) a ∈ A := by
    have := smul_mem_pointwise_smul (d : F ≃ₐ[K] F) a A ha
    rwa [hdA] at this
  refine ⟨hmem, ?_⟩
  rw [inertiaSubgroup, MonoidHom.mem_ker] at hd
  have h := RingEquiv.congr_fun hd (IsLocalRing.residue A ⟨a, ha⟩)
  rw [MulSemiringAction.toRingAut_apply, MulSemiringAction.toRingEquiv_apply,
    ← IsLocalRing.ResidueField.residue_smul, RingAut.one_apply, IsLocalRing.residue_def,
    IsLocalRing.residue_def] at h
  have h2 : d • (⟨a, ha⟩ : A) - ⟨a, ha⟩ ∈ IsLocalRing.maximalIdeal A := Ideal.Quotient.eq.mp h
  rw [valuation_lt_one_iff] at h2
  exact h2

end General
p2m_reactivate "P2MW.S_ValuationSubring_exists_mem_inertiaSubgroupIn_apply_eq_pow_of_pow_prime_pow_eq_one.PrimePowerInertia P2MW.S_ValuationSubring_exists_mem_inertiaSubgroupIn_apply_eq_pow_of_pow_prime_pow_eq_one.PrimePowerInertia.Seam"

section Center

variable (A : ValuationSubring (AlgebraicClosure ℚ)) {p : ℕ}

private def integralClosureToValuationSubring : integralClosure ℤ (AlgebraicClosure ℚ) →+* A :=
  (integralClosure ℤ (AlgebraicClosure ℚ)).val.toRingHom.codRestrict A.toSubring
    (coe_integralClosure_mem A)

private def center : Ideal (integralClosure ℤ (AlgebraicClosure ℚ)) :=
  (IsLocalRing.maximalIdeal A).comap (integralClosureToValuationSubring A)

private theorem mem_center_iff {b : integralClosure ℤ (AlgebraicClosure ℚ)} :
    b ∈ (center A) ↔ A.valuation b < 1 := by
  rw [center, Ideal.mem_comap, valuation_lt_one_iff]
  rfl

private scoped instance center_isPrime : (center A).IsPrime := Ideal.IsPrime.comap _

private theorem natCast_mem_center (hA : A.LiesOverPrime p) :
    (p : integralClosure ℤ (AlgebraicClosure ℚ)) ∈ (center A) := by
  rw [mem_center_iff, ← ValuationSubring.mem_nonunits_iff]
  simpa using (show ((p : ℕ) : AlgebraicClosure ℚ) ∈ A.nonunits from hA)

private theorem valuation_eq_one_of_notMem_center {s : integralClosure ℤ (AlgebraicClosure ℚ)}
    (hs : s ∉ (center A)) : A.valuation s = 1 :=
  le_antisymm ((A.valuation_le_one_iff _).mpr ((coe_integralClosure_mem A) s))
    (not_lt.mp fun h => hs ((mem_center_iff A).mpr h))

private theorem mem_primeBelow_iff_mem_center (L : IntermediateField ℚ (AlgebraicClosure ℚ)) (x : 𝓞 L) :
    x ∈ (primeBelow A) L ↔
      (⟨algebraMap L (AlgebraicClosure ℚ) (x : L), map_isIntegral_int _
        (NumberField.RingOfIntegers.isIntegral_coe x)⟩ :
          integralClosure ℤ (AlgebraicClosure ℚ)) ∈ (center A) := by
  rw [mem_primeBelow_iff, mem_center_iff]

private theorem exists_integralClosure_mul_eq_of_mem (hp : p.Prime) (hA : A.LiesOverPrime p)
    (a : AlgebraicClosure ℚ) (ha : a ∈ A) :
    ∃ x s : integralClosure ℤ (AlgebraicClosure ℚ), s ∉ (center A) ∧
      a * s = x := by
  let F : IntermediateField ℚ (AlgebraicClosure ℚ) := IntermediateField.adjoin ℚ {a}
  haveI : FiniteDimensional ℚ F :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral a)
  let a' : F := ⟨a, IntermediateField.mem_adjoin_simple_self ℚ a⟩
  have ha' : algebraMap F (AlgebraicClosure ℚ) a' = a := rfl
  obtain ⟨x, s, hs, hxs⟩ := (exists_mul_eq_of_mem A) F hp hA a' (ha'.symm ▸ ha)
  refine ⟨⟨algebraMap F (AlgebraicClosure ℚ) (x : F), map_isIntegral_int _
      (NumberField.RingOfIntegers.isIntegral_coe x)⟩,
    ⟨algebraMap F (AlgebraicClosure ℚ) (s : F), map_isIntegral_int _
      (NumberField.RingOfIntegers.isIntegral_coe s)⟩, ?_, ?_⟩
  · rwa [← mem_primeBelow_iff_mem_center]
  · change a * algebraMap F (AlgebraicClosure ℚ) (s : F) = algebraMap F (AlgebraicClosure ℚ) (x : F)
    rw [← ha', ← map_mul, hxs]

private theorem apply_mem_and_valuation_sub_lt_one (hp : p.Prime) (hA : A.LiesOverPrime p)
    (ρ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (hρ : ∀ b : integralClosure ℤ (AlgebraicClosure ℚ),
      A.valuation (ρ b - b) < 1)
    (a : AlgebraicClosure ℚ) (ha : a ∈ A) : ρ a ∈ A ∧ A.valuation (ρ a - a) < 1 := by
  obtain ⟨x, s, hs, hax⟩ := (exists_integralClosure_mul_eq_of_mem A) hp hA a ha
  have hvs : A.valuation (s : AlgebraicClosure ℚ) = 1 := (valuation_eq_one_of_notMem_center A) hs
  have hvx : A.valuation (x : AlgebraicClosure ℚ) ≤ 1 :=
    (A.valuation_le_one_iff _).mpr ((coe_integralClosure_mem A) x)
  set c : AlgebraicClosure ℚ := ρ x - x with hc
  set c' : AlgebraicClosure ℚ := ρ s - s with hc'
  have hvc : A.valuation c < 1 := hρ x
  have hvc' : A.valuation c' < 1 := hρ s
  have hρx : ρ x = x + c := by rw [hc]; ring
  have hρs : ρ s = s + c' := by rw [hc']; ring
  have hlt : A.valuation c' < A.valuation (s : AlgebraicClosure ℚ) := by rw [hvs]; exact hvc'
  have hvρs : A.valuation (ρ s) = 1 := by
    rw [hρs, Valuation.map_add_eq_of_lt_left _ hlt, hvs]
  have hs0 : (s : AlgebraicClosure ℚ) ≠ 0 := fun h => by
    rw [h, map_zero] at hvs; exact zero_ne_one hvs
  have hρs0 : ρ s ≠ 0 := fun h => by
    rw [h, map_zero] at hvρs; exact zero_ne_one hvρs
  have hρa : ρ a = ρ x / ρ s := by
    rw [eq_div_iff hρs0, ← map_mul, hax]
  have hvρx : A.valuation (ρ x) ≤ 1 := by
    rw [hρx]
    exact Valuation.map_add_le _ hvx hvc.le
  refine ⟨?_, ?_⟩
  · rw [← A.valuation_le_one_iff, hρa, map_div₀, hvρs, div_one]
    exact hvρx
  · have ha' : a = x / s := by rw [eq_div_iff hs0, hax]
    have hdiff : ρ a - a = (c * s - x * c') / (ρ s * s) := by
      rw [hρa, ha', hρx, hρs, div_sub_div _ _ (by rw [← hρs]; exact hρs0) hs0]
      congr 1
      ring
    rw [hdiff, map_div₀, map_mul, hvρs, hvs, one_mul, div_one]
    refine Valuation.map_sub_lt _ ?_ ?_
    · rw [map_mul, hvs, mul_one]; exact hvc
    · rw [map_mul]
      calc A.valuation (x : AlgebraicClosure ℚ) * A.valuation c'
          ≤ A.valuation c' := mul_le_of_le_one_left' hvx
        _ < 1 := hvc'

private theorem mem_inertiaSubgroupIn_of_forall_valuation_sub_lt_one (hp : p.Prime)
    (hA : A.LiesOverPrime p) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (hσ : ∀ b : integralClosure ℤ (AlgebraicClosure ℚ), A.valuation (σ b - b) < 1) :
    σ ∈ A.inertiaSubgroupIn ℚ := by
  have key := (apply_mem_and_valuation_sub_lt_one A) hp hA

  have hσinv : ∀ b : integralClosure ℤ (AlgebraicClosure ℚ), A.valuation (σ⁻¹ b - b) < 1 := by
    intro b
    have hb' : IsIntegral ℤ (σ⁻¹ (b : AlgebraicClosure ℚ)) := map_isIntegral_int _ b.2
    have h := hσ ⟨_, hb'⟩
    have e : σ (σ⁻¹ (b : AlgebraicClosure ℚ)) = b := by
      rw [← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]
    change A.valuation (σ (σ⁻¹ (b : AlgebraicClosure ℚ)) - σ⁻¹ b) < 1 at h
    rw [e] at h
    rwa [← Valuation.map_neg, neg_sub]

  have hstab : σ ∈ A.decompositionSubgroup ℚ := by
    rw [decompositionSubgroup, MulAction.mem_stabilizer_iff]
    ext x
    rw [mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def]
    constructor
    · intro hx
      have := (key σ hσ _ hx).1
      rwa [← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply] at this
    · intro hx
      exact (key σ⁻¹ hσinv _ hx).1

  refine Subgroup.mem_map.mpr ⟨⟨σ, hstab⟩, ?_, rfl⟩
  rw [inertiaSubgroup, MonoidHom.mem_ker]
  ext r
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective r
  rw [MulSemiringAction.toRingAut_apply, MulSemiringAction.toRingEquiv_apply,
    ← IsLocalRing.ResidueField.residue_smul, RingAut.one_apply, IsLocalRing.residue_def,
    IsLocalRing.residue_def]
  apply Ideal.Quotient.eq.mpr
  rw [valuation_lt_one_iff]
  exact (key σ hσ a a.2).2

end Center
p2m_reactivate "P2MW.S_ValuationSubring_exists_mem_inertiaSubgroupIn_apply_eq_pow_of_pow_prime_pow_eq_one.PrimePowerInertia P2MW.S_ValuationSubring_exists_mem_inertiaSubgroupIn_apply_eq_pow_of_pow_prime_pow_eq_one.PrimePowerInertia.Seam"

section Lift

variable (A : ValuationSubring (AlgebraicClosure ℚ)) (L : IntermediateField ℚ (AlgebraicClosure ℚ))
  {p : ℕ}

private theorem algebraMap_restrictNormalHom_apply [Normal ℚ L]
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : L) :
    algebraMap L (AlgebraicClosure ℚ) (AlgEquiv.restrictNormalHom L σ x) =
      σ (algebraMap L (AlgebraicClosure ℚ) x) :=
  AlgEquiv.restrictNormal_commutes σ L x

variable [IsGalois ℚ L]

private theorem exists_lift_valuation_sub_lt_one_of_mem_inertia (τ : L ≃ₐ[ℚ] L)
    (hτ : τ ∈ ((primeBelow A) L).inertia (L ≃ₐ[ℚ] L)) :
    ∃ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, AlgEquiv.restrictNormalHom L σ = τ ∧
      ∀ b : integralClosure ℤ (AlgebraicClosure ℚ),
        A.valuation (σ b - b) < 1 := by
  classical
  haveI : Algebra.IsAlgebraic L (AlgebraicClosure ℚ) := Algebra.IsAlgebraic.tower_top (K := ℚ) L
  haveI : Algebra.IsIntegral L (AlgebraicClosure ℚ) :=
    Algebra.isAlgebraic_iff_isIntegral.mp inferInstance
  haveI : Normal L (AlgebraicClosure ℚ) := Normal.tower_top_of_normal ℚ L _
  haveI : Algebra.IsSeparable L (AlgebraicClosure ℚ) :=
    Algebra.isSeparable_tower_top_of_isSeparable ℚ L _
  haveI : IsGalois L (AlgebraicClosure ℚ) := ⟨⟩
  set Q : Ideal (𝓞 L) := (primeBelow A) L with hQdef
  set 𝔔 : Ideal (integralClosure ℤ (AlgebraicClosure ℚ)) := (center A) with h𝔔def
  have hτ' : ∀ x : 𝓞 L, τ • x - x ∈ Q := fun x => (AddSubgroup.mem_inertia.mp hτ) x
  have hstabτ : τ • Q = Q := Ideal.inertia_le_stabilizer Q hτ

  letI actG : MulSemiringAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      (integralClosure ℤ (AlgebraicClosure ℚ)) := inferInstance
  letI actGI : DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      (Ideal (integralClosure ℤ (AlgebraicClosure ℚ))) := Ideal.pointwiseDistribMulAction
  letI mulActGI : MulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      (Ideal (integralClosure ℤ (AlgebraicClosure ℚ))) := DistribMulAction.toMulAction
  letI dsmulGI : DistribSMul (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      (Ideal (integralClosure ℤ (AlgebraicClosure ℚ))) := DistribMulAction.toDistribSMul
  letI smulzGI : SMulZeroClass (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      (Ideal (integralClosure ℤ (AlgebraicClosure ℚ))) := DistribSMul.toSMulZeroClass
  letI smulGI : SMul (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      (Ideal (integralClosure ℤ (AlgebraicClosure ℚ))) := SMulZeroClass.toSMul

  let f : 𝓞 L →+* integralClosure ℤ (AlgebraicClosure ℚ) :=
    (algebraMap (𝓞 L) (AlgebraicClosure ℚ)).codRestrict (integralClosure ℤ (AlgebraicClosure ℚ))
      fun x => (map_isIntegral_int (algebraMap (𝓞 L) (AlgebraicClosure ℚ))
        (Algebra.IsIntegral.isIntegral x))
  letI algOB : Algebra (𝓞 L) (integralClosure ℤ (AlgebraicClosure ℚ)) := f.toAlgebra
  have hf_coe : ∀ x : 𝓞 L, ((algebraMap (𝓞 L) (integralClosure ℤ (AlgebraicClosure ℚ)) x :
      integralClosure ℤ (AlgebraicClosure ℚ)) : AlgebraicClosure ℚ) =
        algebraMap L (AlgebraicClosure ℚ) (x : L) :=
    fun x => rfl
  haveI : IsScalarTower (𝓞 L) (integralClosure ℤ (AlgebraicClosure ℚ)) (AlgebraicClosure ℚ) :=
    IsScalarTower.of_algebraMap_eq fun x => rfl

  have hmemQ : ∀ x : 𝓞 L, algebraMap (𝓞 L) (integralClosure ℤ (AlgebraicClosure ℚ)) x ∈ 𝔔 ↔
      x ∈ Q := fun x => by
    rw [h𝔔def, mem_center_iff, hf_coe, hQdef, mem_primeBelow_iff]
  haveI h𝔔lies : 𝔔.LiesOver Q := ⟨by
    ext x
    rw [Ideal.under_def, Ideal.mem_comap, hmemQ]⟩

  have hres : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : 𝓞 L),
      σ • algebraMap (𝓞 L) (integralClosure ℤ (AlgebraicClosure ℚ)) x =
        algebraMap (𝓞 L) (integralClosure ℤ (AlgebraicClosure ℚ))
          ((AlgEquiv.restrictNormalHom L σ) • x) := by
    intro σ x
    apply Subtype.ext
    change σ (algebraMap L (AlgebraicClosure ℚ) (x : L)) =
      algebraMap L (AlgebraicClosure ℚ) ((σ.restrictNormal L) (x : L))
    exact (AlgEquiv.restrictNormal_commutes σ L (x : L)).symm

  let rsh : (AlgebraicClosure ℚ ≃ₐ[L] AlgebraicClosure ℚ) →*
      (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :=
    { toFun := fun g => g.restrictScalars ℚ
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hrsh_apply : ∀ (g : AlgebraicClosure ℚ ≃ₐ[L] AlgebraicClosure ℚ) (x : AlgebraicClosure ℚ),
      rsh g x = g x := fun _ _ => rfl

  have hresL : ∀ g : AlgebraicClosure ℚ ≃ₐ[L] AlgebraicClosure ℚ,
      AlgEquiv.restrictNormalHom L (rsh g) = 1 := by
    intro g
    refine AlgEquiv.ext fun x => (algebraMap L (AlgebraicClosure ℚ)).injective ?_
    change algebraMap L (AlgebraicClosure ℚ) (((rsh g).restrictNormal L) x) =
      algebraMap L (AlgebraicClosure ℚ) x
    rw [AlgEquiv.restrictNormal_commutes, hrsh_apply]
    exact g.commutes x
  letI actL : MulSemiringAction (AlgebraicClosure ℚ ≃ₐ[L] AlgebraicClosure ℚ)
      (integralClosure ℤ (AlgebraicClosure ℚ)) := MulSemiringAction.compHom _ rsh
  letI actLI : DistribMulAction (AlgebraicClosure ℚ ≃ₐ[L] AlgebraicClosure ℚ)
      (Ideal (integralClosure ℤ (AlgebraicClosure ℚ))) := Ideal.pointwiseDistribMulAction
  letI mulActLI : MulAction (AlgebraicClosure ℚ ≃ₐ[L] AlgebraicClosure ℚ)
      (Ideal (integralClosure ℤ (AlgebraicClosure ℚ))) := DistribMulAction.toMulAction
  letI dsmulLI : DistribSMul (AlgebraicClosure ℚ ≃ₐ[L] AlgebraicClosure ℚ)
      (Ideal (integralClosure ℤ (AlgebraicClosure ℚ))) := DistribMulAction.toDistribSMul
  letI smulzLI : SMulZeroClass (AlgebraicClosure ℚ ≃ₐ[L] AlgebraicClosure ℚ)
      (Ideal (integralClosure ℤ (AlgebraicClosure ℚ))) := DistribSMul.toSMulZeroClass
  letI smulLI : SMul (AlgebraicClosure ℚ ≃ₐ[L] AlgebraicClosure ℚ)
      (Ideal (integralClosure ℤ (AlgebraicClosure ℚ))) := SMulZeroClass.toSMul
  have hrs : ∀ (g : AlgebraicClosure ℚ ≃ₐ[L] AlgebraicClosure ℚ)
      (b : integralClosure ℤ (AlgebraicClosure ℚ)), g • b = rsh g • b := fun _ _ => rfl
  have hrsI : ∀ (g : AlgebraicClosure ℚ ≃ₐ[L] AlgebraicClosure ℚ)
      (J : Ideal (integralClosure ℤ (AlgebraicClosure ℚ))), g • J = rsh g • J := by
    intro g J
    ext b
    rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem, Ideal.mem_pointwise_smul_iff_inv_smul_mem,
      ← map_inv, hrs]

  haveI : SMulCommClass (AlgebraicClosure ℚ ≃ₐ[L] AlgebraicClosure ℚ) (𝓞 L)
      (integralClosure ℤ (AlgebraicClosure ℚ)) := ⟨fun g a b => by
    apply Subtype.ext
    change g ((algebraMap L (AlgebraicClosure ℚ) (a : L)) * (b : AlgebraicClosure ℚ)) =
      algebraMap L (AlgebraicClosure ℚ) (a : L) * g (b : AlgebraicClosure ℚ)
    rw [map_mul, AlgEquiv.commutes]⟩
  letI : TopologicalSpace (integralClosure ℤ (AlgebraicClosure ℚ)) := ⊥
  haveI : DiscreteTopology (integralClosure ℤ (AlgebraicClosure ℚ)) := ⟨rfl⟩
  haveI : ContinuousSMul (AlgebraicClosure ℚ ≃ₐ[L] AlgebraicClosure ℚ)
      (integralClosure ℤ (AlgebraicClosure ℚ)) := by
    refine continuousSMul_iff_stabilizer_isOpen.mpr fun b => ?_
    haveI : FiniteDimensional L (IntermediateField.adjoin L {(b : AlgebraicClosure ℚ)}) :=
      IntermediateField.adjoin.finiteDimensional
        (Algebra.IsIntegral.isIntegral (b : AlgebraicClosure ℚ))
    refine Subgroup.isOpen_mono ?_
      (IntermediateField.fixingSubgroup_isOpen
        (IntermediateField.adjoin L {(b : AlgebraicClosure ℚ)}))
    intro g hg
    rw [MulAction.mem_stabilizer_iff]
    apply Subtype.ext
    change g (b : AlgebraicClosure ℚ) = b
    rw [IntermediateField.mem_fixingSubgroup_iff] at hg
    exact hg _ (IntermediateField.mem_adjoin_simple_self L (b : AlgebraicClosure ℚ))
  haveI : Algebra.IsInvariant (𝓞 L) (integralClosure ℤ (AlgebraicClosure ℚ))
      (AlgebraicClosure ℚ ≃ₐ[L] AlgebraicClosure ℚ) := ⟨fun b hb => by
    have hb' : (b : AlgebraicClosure ℚ) ∈ Set.range (algebraMap L (AlgebraicClosure ℚ)) := by
      rw [InfiniteGalois.mem_range_algebraMap_iff_fixed]
      intro g
      exact congrArg (fun z : integralClosure ℤ (AlgebraicClosure ℚ) => (z : AlgebraicClosure ℚ))
        (hb g)
    obtain ⟨y, hy⟩ := hb'
    have hyint : IsIntegral ℤ y := by
      obtain ⟨q, hq, hq0⟩ := (b.2 : IsIntegral ℤ (b : AlgebraicClosure ℚ))
      refine ⟨q, hq, (algebraMap L (AlgebraicClosure ℚ)).injective ?_⟩
      rw [Polynomial.hom_eval₂, map_zero, hy]
      convert hq0 using 2 <;> first | rfl | exact Subsingleton.elim _ _
    refine ⟨⟨y, hyint⟩, Subtype.ext ?_⟩
    rw [hf_coe]
    exact hy⟩

  obtain ⟨σ₀, hσ₀⟩ := AlgEquiv.restrictNormalHom_surjective (K₁ := L) (AlgebraicClosure ℚ) τ
  have hunder : Ideal.under (𝓞 L) (σ₀ • 𝔔 : Ideal (integralClosure ℤ (AlgebraicClosure ℚ))) =
      Ideal.under (𝓞 L) 𝔔 := by
    ext x
    rw [Ideal.mem_under, Ideal.mem_under, Ideal.mem_pointwise_smul_iff_inv_smul_mem, hres,
      hmemQ, hmemQ, map_inv, hσ₀]
    conv_rhs => rw [← hstabτ]
    rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem]
  obtain ⟨g, hg⟩ := Algebra.IsInvariant.exists_smul_of_under_eq_of_profinite
      (A := 𝓞 L) (G := AlgebraicClosure ℚ ≃ₐ[L] AlgebraicClosure ℚ)
      (σ₀ • 𝔔 : Ideal (integralClosure ℤ (AlgebraicClosure ℚ))) 𝔔 hunder

  have hσ₁𝔔 : (rsh g * σ₀) • 𝔔 = 𝔔 := by rw [mul_smul, ← hrsI, ← hg]
  have hσ₁L : AlgEquiv.restrictNormalHom L (rsh g * σ₀) = τ := by
    rw [map_mul, hresL, one_mul, hσ₀]

  have hσ₁stab : rsh g * σ₀ ∈
      MulAction.stabilizer (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) 𝔔 := hσ₁𝔔
  let φ₀ : (integralClosure ℤ (AlgebraicClosure ℚ) ⧸ 𝔔) ≃ₐ[ℤ ⧸ 𝔔.under ℤ]
      (integralClosure ℤ (AlgebraicClosure ℚ) ⧸ 𝔔) :=
    Ideal.Quotient.stabilizerHom 𝔔 (𝔔.under ℤ) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      ⟨rsh g * σ₀, hσ₁stab⟩
  have hστQ : ∀ x : 𝓞 L, Ideal.Quotient.mk 𝔔 ((rsh g * σ₀) •
      algebraMap (𝓞 L) (integralClosure ℤ (AlgebraicClosure ℚ)) x) =
        Ideal.Quotient.mk 𝔔 (algebraMap (𝓞 L) (integralClosure ℤ (AlgebraicClosure ℚ)) x) := by
    intro x
    rw [Ideal.Quotient.eq, hres, hσ₁L, ← map_sub, hmemQ]
    exact hτ' x
  let φ : (integralClosure ℤ (AlgebraicClosure ℚ) ⧸ 𝔔) ≃ₐ[𝓞 L ⧸ Q]
      (integralClosure ℤ (AlgebraicClosure ℚ) ⧸ 𝔔) :=
    AlgEquiv.ofRingEquiv (f := (φ₀ : (integralClosure ℤ (AlgebraicClosure ℚ) ⧸ 𝔔) ≃+*
      (integralClosure ℤ (AlgebraicClosure ℚ) ⧸ 𝔔))) (by
      intro a
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective a
      rw [Ideal.Quotient.algebraMap_mk_of_liesOver]
      exact hστQ x)
  have hφ : ∀ b : integralClosure ℤ (AlgebraicClosure ℚ),
      φ (Ideal.Quotient.mk 𝔔 b) = Ideal.Quotient.mk 𝔔 ((rsh g * σ₀) • b) :=
    fun b => rfl
  obtain ⟨t, ht⟩ :=
    Ideal.Quotient.stabilizerHom_surjective_of_profinite
      (G := AlgebraicClosure ℚ ≃ₐ[L] AlgebraicClosure ℚ) Q 𝔔 φ
  have ht' : ∀ b : integralClosure ℤ (AlgebraicClosure ℚ),
      Ideal.Quotient.mk 𝔔 ((t : AlgebraicClosure ℚ ≃ₐ[L] AlgebraicClosure ℚ) • b) =
        Ideal.Quotient.mk 𝔔 ((rsh g * σ₀) • b) := by
    intro b
    have h := congrArg (fun e => e (Ideal.Quotient.mk 𝔔 b)) ht
    simpa only [Ideal.Quotient.stabilizerHom_apply, hφ, Subgroup.smul_def, Submonoid.smul_def] using h

  refine ⟨(rsh (t : AlgebraicClosure ℚ ≃ₐ[L] AlgebraicClosure ℚ))⁻¹ * (rsh g * σ₀), ?_, ?_⟩
  · rw [map_mul, map_inv, hresL, inv_one, one_mul, hσ₁L]
  · intro b
    have h1 : (rsh g * σ₀) • b - (t : AlgebraicClosure ℚ ≃ₐ[L] AlgebraicClosure ℚ) • b ∈ 𝔔 := by
      rw [← Ideal.Quotient.eq]
      exact (ht' b).symm
    have h2 : ((t⁻¹ : MulAction.stabilizer (AlgebraicClosure ℚ ≃ₐ[L] AlgebraicClosure ℚ) 𝔔) :
        AlgebraicClosure ℚ ≃ₐ[L] AlgebraicClosure ℚ) •
          ((rsh g * σ₀) • b - (t : AlgebraicClosure ℚ ≃ₐ[L] AlgebraicClosure ℚ) • b) ∈ 𝔔 := by
      have hmem := (Ideal.smul_mem_pointwise_smul_iff
        (a := ((t⁻¹ : MulAction.stabilizer (AlgebraicClosure ℚ ≃ₐ[L] AlgebraicClosure ℚ) 𝔔) :
          AlgebraicClosure ℚ ≃ₐ[L] AlgebraicClosure ℚ))).mpr h1
      rwa [MulAction.mem_stabilizer_iff.mp (t⁻¹).2] at hmem
    have h3 : ((t⁻¹ : MulAction.stabilizer (AlgebraicClosure ℚ ≃ₐ[L] AlgebraicClosure ℚ) 𝔔) :
        AlgebraicClosure ℚ ≃ₐ[L] AlgebraicClosure ℚ) •
          ((rsh g * σ₀) • b - (t : AlgebraicClosure ℚ ≃ₐ[L] AlgebraicClosure ℚ) • b) =
        ((rsh (t : AlgebraicClosure ℚ ≃ₐ[L] AlgebraicClosure ℚ))⁻¹ * (rsh g * σ₀)) • b - b := by
      rw [Subgroup.coe_inv, smul_sub, inv_smul_smul, hrs, map_inv]
      simp only [mul_smul]
    rw [h3] at h2
    exact (mem_center_iff A).mp h2

private theorem exists_mem_inertiaSubgroupIn_restrictNormalHom_eq (hp : p.Prime) (hA : A.LiesOverPrime p)
    (τ : L ≃ₐ[ℚ] L) (hτ : τ ∈ ((primeBelow A) L).inertia (L ≃ₐ[ℚ] L)) :
    ∃ σ ∈ A.inertiaSubgroupIn ℚ, AlgEquiv.restrictNormalHom L σ = τ := by
  obtain ⟨σ, hσL, hσ⟩ := (exists_lift_valuation_sub_lt_one_of_mem_inertia A) L τ hτ
  exact ⟨σ, (mem_inertiaSubgroupIn_of_forall_valuation_sub_lt_one A) hp hA σ hσ, hσL⟩

end Lift
p2m_reactivate "P2MW.S_ValuationSubring_exists_mem_inertiaSubgroupIn_apply_eq_pow_of_pow_prime_pow_eq_one.PrimePowerInertia P2MW.S_ValuationSubring_exists_mem_inertiaSubgroupIn_apply_eq_pow_of_pow_prime_pow_eq_one.PrimePowerInertia.Seam"

section Dictionary

variable (A : ValuationSubring (AlgebraicClosure ℚ)) (L : IntermediateField ℚ (AlgebraicClosure ℚ))
  {p : ℕ}

private theorem coe_smul_ringOfIntegers (τ : L ≃ₐ[ℚ] L) (x : 𝓞 L) : ((τ • x : 𝓞 L) : L) = τ (x : L) :=
  rfl

variable [IsGalois ℚ L]

private theorem map_restrictNormalHom_inertiaSubgroupIn_le :
    (A.inertiaSubgroupIn ℚ).map (AlgEquiv.restrictNormalHom L) ≤
      ((primeBelow A) L).inertia (L ≃ₐ[ℚ] L) := by
  rintro _ ⟨σ, hσ, rfl⟩
  refine AddSubgroup.mem_inertia.mpr fun x => ?_
  change AlgEquiv.restrictNormalHom L σ • x - x ∈ (primeBelow A) L
  rw [mem_primeBelow_iff]
  have hcoe : (((AlgEquiv.restrictNormalHom L σ • x - x : 𝓞 L)) : L) =
      AlgEquiv.restrictNormalHom L σ (x : L) - x := rfl
  rw [hcoe, map_sub, algebraMap_restrictNormalHom_apply]
  exact (valuation_sub_lt_one_of_mem_inertiaSubgroupIn' A hσ
    ((algebraMap_ringOfIntegers_mem A) L x)).2

private theorem map_restrictNormalHom_inertiaSubgroupIn_eq_inertia (hp : p.Prime) (hA : A.LiesOverPrime p) :
    (A.inertiaSubgroupIn ℚ).map (AlgEquiv.restrictNormalHom L) =
      ((primeBelow A) L).inertia (L ≃ₐ[ℚ] L) := by
  refine le_antisymm ((map_restrictNormalHom_inertiaSubgroupIn_le A) L) fun τ hτ => ?_
  obtain ⟨σ, hσ, rfl⟩ := (exists_mem_inertiaSubgroupIn_restrictNormalHom_eq A) L hp hA τ hτ
  exact Subgroup.mem_map_of_mem _ hσ

variable [FiniteDimensional ℚ L]

attribute [local instance] Ideal.Quotient.field in

private theorem card_inertia_primeBelow_eq_ramificationIdx (hp : p.Prime) (hA : A.LiesOverPrime p) :
    Nat.card (((primeBelow A) L).inertia (L ≃ₐ[ℚ] L)) =
      Ideal.ramificationIdx' (Ideal.span {(p : ℤ)}) ((primeBelow A) L) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI := (primeBelow_liesOver A) L hp hA
  haveI := (isMaximal_primeBelow A) L hp hA
  rw [Ideal.card_inertia_eq_ramificationIdxIn (G := L ≃ₐ[ℚ] L) (Ideal.span {(p : ℤ)}) ((primeBelow A) L),
    Ideal.ramificationIdxIn_eq_ramificationIdx (Ideal.span {(p : ℤ)}) ((primeBelow A) L)
      (L ≃ₐ[ℚ] L)]
  exact (Ideal.ramificationIdx'_eq_ramificationIdx (p := Ideal.span {(p : ℤ)}) ((primeBelow A) L)
    (by simpa [Ideal.span_singleton_eq_bot] using hp.ne_zero)).symm

private theorem card_map_restrictNormalHom_inertiaSubgroupIn (hp : p.Prime) (hA : A.LiesOverPrime p) :
    Nat.card ((A.inertiaSubgroupIn ℚ).map (AlgEquiv.restrictNormalHom L)) =
      Ideal.ramificationIdx' (Ideal.span {(p : ℤ)}) ((primeBelow A) L) := by
  rw [(map_restrictNormalHom_inertiaSubgroupIn_eq_inertia A) L hp hA,
    (card_inertia_primeBelow_eq_ramificationIdx A) L hp hA]

private theorem dvd_card_map_restrictNormalHom_inertiaSubgroupIn (hp : p.Prime) (hA : A.LiesOverPrime p)
    (z : L) {m a : ℕ} (hm : 0 < m) (hcop : Nat.Coprime a m)
    (hval : A.valuation (algebraMap L (AlgebraicClosure ℚ) z) ^ m =
      A.valuation (p : AlgebraicClosure ℚ) ^ a) :
    m ∣ Nat.card ((A.inertiaSubgroupIn ℚ).map (AlgEquiv.restrictNormalHom L)) := by
  rw [(card_map_restrictNormalHom_inertiaSubgroupIn A) L hp hA]
  exact (dvd_ramificationIdx_of_valuation_pow_eq A) L hp hA z hm hcop hval

end Dictionary
p2m_reactivate "P2MW.S_ValuationSubring_exists_mem_inertiaSubgroupIn_apply_eq_pow_of_pow_prime_pow_eq_one.PrimePowerInertia P2MW.S_ValuationSubring_exists_mem_inertiaSubgroupIn_apply_eq_pow_of_pow_prime_pow_eq_one.PrimePowerInertia.Seam"

section PrimePowerCyclotomic

variable (A : ValuationSubring (AlgebraicClosure ℚ))

private theorem valuation_one_sub_pow_le {ζ : AlgebraicClosure ℚ} (hζ : IsIntegral ℤ ζ) (i : ℕ) :
    A.valuation (1 - ζ ^ i) ≤ A.valuation (1 - ζ) := by
  have hζA : ζ ∈ A := (mem_of_isIntegral_int A) hζ
  have hS : (∑ j ∈ Finset.range i, ζ ^ j) ∈ A := sum_mem fun j _ => pow_mem hζA j
  rw [← geom_sum_mul_neg ζ i, map_mul]
  calc A.valuation (∑ j ∈ Finset.range i, ζ ^ j) * A.valuation (1 - ζ)
      ≤ 1 * A.valuation (1 - ζ) := mul_le_mul_left ((A.valuation_le_one_iff _).mpr hS) _
    _ = A.valuation (1 - ζ) := one_mul _

private theorem valuation_one_sub_eq_of_mem_primitiveRoots {n : ℕ} (hn : 0 < n)
    {ζ μ : AlgebraicClosure ℚ} (hζ : IsPrimitiveRoot ζ n)
    (hμ : μ ∈ primitiveRoots n (AlgebraicClosure ℚ)) :
    A.valuation (1 - μ) = A.valuation (1 - ζ) := by
  haveI : NeZero n := ⟨hn.ne'⟩
  have hμ' : IsPrimitiveRoot μ n := (mem_primitiveRoots hn).mp hμ
  obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hμ'.pow_eq_one
  obtain ⟨j, -, hj⟩ := hμ'.eq_pow_of_pow_eq_one hζ.pow_eq_one
  refine le_antisymm ((valuation_one_sub_pow_le A) (hζ.isIntegral hn) i) ?_
  calc A.valuation (1 - ζ) = A.valuation (1 - (ζ ^ i) ^ j) := by rw [hj]
    _ ≤ A.valuation (1 - ζ ^ i) := (valuation_one_sub_pow_le A) ((hζ.isIntegral hn).pow i) j

private theorem valuation_one_sub_pow_totient_eq {p : ℕ} (hp : p.Prime) {k : ℕ} (hk : 0 < k)
    {ζ : AlgebraicClosure ℚ} (hζ : IsPrimitiveRoot ζ (p ^ k)) :
    A.valuation (1 - ζ) ^ Nat.totient (p ^ k) = A.valuation (p : AlgebraicClosure ℚ) := by
  haveI := Fact.mk hp
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, (Nat.sub_add_cancel hk).symm⟩
  have hpos : 0 < p ^ (k' + 1) := pow_pos hp.pos _
  have hprod : (p : AlgebraicClosure ℚ) =
      ∏ μ ∈ primitiveRoots (p ^ (k' + 1)) (AlgebraicClosure ℚ), (1 - μ) := by
    have h := Polynomial.eval_one_cyclotomic_prime_pow (R := AlgebraicClosure ℚ) (p := p) k'
    rw [Polynomial.cyclotomic_eq_prod_X_sub_primitiveRoots hζ, Polynomial.eval_prod] at h
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at h
    exact h.symm
  rw [hprod, map_prod,
    Finset.prod_congr rfl fun μ hμ => (valuation_one_sub_eq_of_mem_primitiveRoots A) hpos hζ hμ,
    Finset.prod_const, hζ.card_primitiveRoots]

end PrimePowerCyclotomic
p2m_reactivate "P2MW.S_ValuationSubring_exists_mem_inertiaSubgroupIn_apply_eq_pow_of_pow_prime_pow_eq_one.PrimePowerInertia P2MW.S_ValuationSubring_exists_mem_inertiaSubgroupIn_apply_eq_pow_of_pow_prime_pow_eq_one.PrimePowerInertia.Seam"

end PrimePowerInertia
p2m_reactivate "P2MW.S_ValuationSubring_exists_mem_inertiaSubgroupIn_apply_eq_pow_of_pow_prime_pow_eq_one.PrimePowerInertia P2MW.S_ValuationSubring_exists_mem_inertiaSubgroupIn_apply_eq_pow_of_pow_prime_pow_eq_one.PrimePowerInertia.Seam"

end
p2m_reactivate "P2MW.S_ValuationSubring_exists_mem_inertiaSubgroupIn_apply_eq_pow_of_pow_prime_pow_eq_one.PrimePowerInertia P2MW.S_ValuationSubring_exists_mem_inertiaSubgroupIn_apply_eq_pow_of_pow_prime_pow_eq_one.PrimePowerInertia.Seam"

theorem solution
    (A : ValuationSubring (AlgebraicClosure ℚ)) {p : ℕ} (hp : p.Prime) (hA : A.LiesOverPrime p)
    (k : ℕ) (a : (ZMod (p ^ k))ˣ) :
    ∃ σ ∈ A.inertiaSubgroupIn ℚ, ∀ μ : AlgebraicClosure ℚ, μ ^ p ^ k = 1 →
      σ μ = μ ^ (a : ZMod (p ^ k)).val := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · refine ⟨1, Subgroup.one_mem _, fun μ hμ => ?_⟩
    rw [pow_zero, pow_one] at hμ
    subst hμ
    rw [one_pow]
    exact map_one _
  haveI : NeZero (p ^ k) := ⟨(pow_pos hp.pos k).ne'⟩

  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure ℚ) (p ^ k)
  let L : IntermediateField ℚ (AlgebraicClosure ℚ) := IntermediateField.adjoin ℚ {ζ}
  haveI : FiniteDimensional ℚ L :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral ζ)
  haveI : IsCyclotomicExtension {p ^ k} ℚ L :=
    hζ.intermediateField_adjoin_isCyclotomicExtension ℚ
  haveI : IsGalois ℚ L := IsCyclotomicExtension.isGalois {p ^ k} ℚ L
  let ζL : L := ⟨ζ, IntermediateField.mem_adjoin_simple_self ℚ ζ⟩
  have hζL : IsPrimitiveRoot ζL (p ^ k) :=
    IsPrimitiveRoot.of_map_of_injective (f := algebraMap L (AlgebraicClosure ℚ)) hζ
      (algebraMap L (AlgebraicClosure ℚ)).injective

  have hval : A.valuation (algebraMap L (AlgebraicClosure ℚ) (1 - ζL)) ^ Nat.totient (p ^ k) =
      A.valuation ((p : ℕ) : AlgebraicClosure ℚ) ^ 1 := by
    have hmap : algebraMap L (AlgebraicClosure ℚ) (1 - ζL) = 1 - ζ := by
      rw [map_sub, map_one]; rfl
    rw [hmap, pow_one, PrimePowerInertia.valuation_one_sub_pow_totient_eq A hp hk hζ]

  have hdvd : Nat.totient (p ^ k) ∣
      Nat.card ((A.inertiaSubgroupIn ℚ).map (AlgEquiv.restrictNormalHom L)) :=
    PrimePowerInertia.dvd_card_map_restrictNormalHom_inertiaSubgroupIn A L hp hA (1 - ζL)
      (Nat.totient_pos.mpr (pow_pos hp.pos k)) (Nat.coprime_one_left _) hval

  have hGcard : Nat.card (L ≃ₐ[ℚ] L) = Nat.totient (p ^ k) := by
    rw [IsGalois.card_aut_eq_finrank,
      IsCyclotomicExtension.finrank (K := ℚ) (n := p ^ k) L
        (Polynomial.cyclotomic.irreducible_rat (pow_pos hp.pos k))]
  have himtop : (A.inertiaSubgroupIn ℚ).map (AlgEquiv.restrictNormalHom L) = ⊤ := by
    refine Subgroup.eq_top_of_card_eq _ ?_
    have hdvd' := Subgroup.card_subgroup_dvd_card
      ((A.inertiaSubgroupIn ℚ).map (AlgEquiv.restrictNormalHom L))
    rw [hGcard] at hdvd' ⊢
    exact Nat.dvd_antisymm hdvd' hdvd

  let χ := hζL.autToPow ℚ
  have hχ : Function.Bijective χ := by
    refine (Nat.bijective_iff_injective_and_card χ).mpr ⟨hζL.autToPow_injective ℚ, ?_⟩
    rw [IsGalois.card_aut_eq_finrank,
      IsCyclotomicExtension.finrank (K := ℚ) (n := p ^ k) L
        (Polynomial.cyclotomic.irreducible_rat (pow_pos hp.pos k)),
      Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
  obtain ⟨τ, hτ⟩ := hχ.2 a
  have hτζ : τ ζL = ζL ^ (a : ZMod (p ^ k)).val := by
    rw [← hτ]
    exact (hζL.autToPow_spec ℚ τ).symm

  have hτmem : τ ∈ (A.inertiaSubgroupIn ℚ).map (AlgEquiv.restrictNormalHom L) := by
    rw [himtop]; exact Subgroup.mem_top τ
  obtain ⟨σ, hσ, hσL⟩ := Subgroup.mem_map.mp hτmem
  refine ⟨σ, hσ, ?_⟩
  have hσζ : σ ζ = ζ ^ (a : ZMod (p ^ k)).val := by
    change σ (algebraMap L (AlgebraicClosure ℚ) ζL) =
      (algebraMap L (AlgebraicClosure ℚ) ζL) ^ (a : ZMod (p ^ k)).val
    rw [← PrimePowerInertia.algebraMap_restrictNormalHom_apply L σ ζL, hσL, hτζ, map_pow]

  intro μ hμ
  obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hμ
  rw [map_pow, hσζ, ← pow_mul, ← pow_mul, mul_comm]

end S_ValuationSubring_exists_mem_inertiaSubgroupIn_apply_eq_pow_of_pow_prime_pow_eq_one
end P2MW
export P2MW.S_ValuationSubring_exists_mem_inertiaSubgroupIn_apply_eq_pow_of_pow_prime_pow_eq_one (solution)
