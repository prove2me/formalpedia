-- Prove2me | solution 1 for ValuationSubring.exists_ideal_ringOfIntegers_inertia_eq_map_restrictNormalHom
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/990f5c0e-66f4-5e49-aa02-19df33e5fe85

import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_exists_ideal_ringOfIntegers_inertia_eq_map_restrictNormalHom

set_option maxHeartbeats 0
set_option synthInstance.maxHeartbeats 1600000

open scoped NumberField Pointwise

noncomputable section

namespace B6Inertia

scoped instance instNormal_rat : Normal ℚ (AlgebraicClosure ℚ) := by
  have h : @Normal ℚ (AlgebraicClosure ℚ) _ _ (AlgebraicClosure.instAlgebra ℚ) := inferInstance
  exact h

scoped instance instAlgebraIsAlgebraic_rat : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := by
  have h : @Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) _ _ (AlgebraicClosure.instAlgebra ℚ) :=
    inferInstance
  exact h

scoped instance instAlgebraIsSeparable_rat : Algebra.IsSeparable ℚ (AlgebraicClosure ℚ) := by
  have h : @Algebra.IsSeparable ℚ (AlgebraicClosure ℚ) _ _ (AlgebraicClosure.instAlgebra ℚ) :=
    inferInstance
  exact h

scoped instance instAlgebraIsIntegral_rat : Algebra.IsIntegral ℚ (AlgebraicClosure ℚ) :=
  Algebra.isAlgebraic_iff_isIntegral.mp inferInstance

scoped instance instIsGalois_rat : IsGalois ℚ (AlgebraicClosure ℚ) := ⟨⟩

scoped instance instNumberField_intermediateField (L : IntermediateField ℚ (AlgebraicClosure ℚ))
    [FiniteDimensional ℚ L] : NumberField L where
  to_charZero := charZero_of_injective_algebraMap (algebraMap ℚ L).injective
  to_finiteDimensional := inferInstance

end B6Inertia
p2m_reactivate "P2MW.S_ValuationSubring_exists_ideal_ringOfIntegers_inertia_eq_map_restrictNormalHom.B6Inertia"

namespace ValuationSubring
p2m_export "ValuationSubring" "comap subtype mem_comap neg_mem smul_mem_pointwise_smul_iff inertiaSubgroup toSubring algebraMap_apply ext zero_mem nonunits mem_nonunits_iff valuation_le_one mk smul_mem_pointwise_smul mem_top mul_mem valuation_lt_one_iff mem_pointwise_smul_iff_inv_smul_mem add_mem decompositionSubgroup valuation_le_one_iff algebra valuation LiesOverPrime inertiaSubgroupIn"
p2m_open "ValuationSubring"

section Integers

variable (A : ValuationSubring (AlgebraicClosure ℚ))

private theorem _root_.ValuationSubring.mem_of_isIntegral_int {b : AlgebraicClosure ℚ} (hb : IsIntegral ℤ b) : b ∈ A := by
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

p2m_export "ValuationSubring" "mem_of_isIntegral_int"

private theorem _root_.ValuationSubring.coe_integralClosure_mem (b : integralClosure ℤ (AlgebraicClosure ℚ)) :
    (b : AlgebraicClosure ℚ) ∈ A :=
  A.mem_of_isIntegral_int b.2

p2m_export "ValuationSubring" "coe_integralClosure_mem"
variable (L : IntermediateField ℚ (AlgebraicClosure ℚ))

private theorem _root_.ValuationSubring.algebraMap_ringOfIntegers_mem (x : 𝓞 L) :
    algebraMap L (AlgebraicClosure ℚ) (x : L) ∈ A :=
  A.mem_of_isIntegral_int
    (map_isIntegral_int (algebraMap L (AlgebraicClosure ℚ))
      (NumberField.RingOfIntegers.isIntegral_coe x))

p2m_export "ValuationSubring" "algebraMap_ringOfIntegers_mem"

private theorem _root_.ValuationSubring.valuation_algebraMap_ringOfIntegers_le_one (x : 𝓞 L) :
    A.valuation (algebraMap L (AlgebraicClosure ℚ) (x : L)) ≤ 1 :=
  (A.valuation_le_one_iff _).mpr (A.algebraMap_ringOfIntegers_mem L x)

p2m_export "ValuationSubring" "valuation_algebraMap_ringOfIntegers_le_one"

private def _root_.ValuationSubring.ringOfIntegersToValuationSubring : 𝓞 L →+* A :=
  ((algebraMap L (AlgebraicClosure ℚ)).comp (algebraMap (𝓞 L) L)).codRestrict A.toSubring
    (fun x => A.algebraMap_ringOfIntegers_mem L x)

p2m_export "ValuationSubring" "ringOfIntegersToValuationSubring"
@[scoped simp] theorem coe_ringOfIntegersToValuationSubring (x : 𝓞 L) :
    (A.ringOfIntegersToValuationSubring L x : AlgebraicClosure ℚ) =
      algebraMap L (AlgebraicClosure ℚ) (x : L) := rfl

private def _root_.ValuationSubring.primeBelow : Ideal (𝓞 L) :=
  (IsLocalRing.maximalIdeal A).comap (A.ringOfIntegersToValuationSubring L)

p2m_export "ValuationSubring" "primeBelow"
private theorem _root_.ValuationSubring.mem_primeBelow_iff {x : 𝓞 L} :
    x ∈ A.primeBelow L ↔ A.valuation (algebraMap L (AlgebraicClosure ℚ) (x : L)) < 1 := by
  rw [primeBelow, Ideal.mem_comap, valuation_lt_one_iff]
  rfl

p2m_export "ValuationSubring" "mem_primeBelow_iff"
theorem mem_primeBelow_iff_mem_nonunits {x : 𝓞 L} :
    x ∈ A.primeBelow L ↔ algebraMap L (AlgebraicClosure ℚ) (x : L) ∈ A.nonunits := by
  rw [mem_primeBelow_iff, mem_nonunits_iff]

private theorem _root_.ValuationSubring.notMem_primeBelow_iff {x : 𝓞 L} :
    x ∉ A.primeBelow L ↔ A.valuation (algebraMap L (AlgebraicClosure ℚ) (x : L)) = 1 := by
  rw [mem_primeBelow_iff, not_lt]
  exact ⟨fun h => le_antisymm (A.valuation_algebraMap_ringOfIntegers_le_one L x) h,
    fun h => h.ge⟩

p2m_export "ValuationSubring" "notMem_primeBelow_iff"
private scoped instance _root_.ValuationSubring.primeBelow_isPrime : (A.primeBelow L).IsPrime :=
  Ideal.IsPrime.comap _

p2m_export "ValuationSubring" "primeBelow_isPrime"
variable {p : ℕ}

private theorem _root_.ValuationSubring.natCast_mem_primeBelow (hA : A.LiesOverPrime p) : (p : 𝓞 L) ∈ A.primeBelow L := by
  rw [mem_primeBelow_iff_mem_nonunits]
  change algebraMap L (AlgebraicClosure ℚ) (algebraMap (𝓞 L) L (p : 𝓞 L)) ∈ A.nonunits
  rw [map_natCast, map_natCast]
  exact hA

p2m_export "ValuationSubring" "natCast_mem_primeBelow"
private theorem _root_.ValuationSubring.primeBelow_ne_bot (hp : p.Prime) (hA : A.LiesOverPrime p) : A.primeBelow L ≠ ⊥ := by
  intro h
  have := A.natCast_mem_primeBelow L hA
  rw [h, Ideal.mem_bot, Nat.cast_eq_zero] at this
  exact hp.ne_zero this

p2m_export "ValuationSubring" "primeBelow_ne_bot"
theorem span_natCast_isMaximal (hp : p.Prime) : (Ideal.span {(p : ℤ)}).IsMaximal :=
  ((Ideal.span_singleton_prime (Int.natCast_ne_zero.mpr hp.ne_zero)).mpr
    (Nat.prime_iff_prime_int.mp hp)).isMaximal
    (by simpa [Ideal.span_singleton_eq_bot] using hp.ne_zero)

private theorem _root_.ValuationSubring.under_int_primeBelow (hp : p.Prime) (hA : A.LiesOverPrime p) :
    (A.primeBelow L).under ℤ = Ideal.span {(p : ℤ)} := by
  refine ((span_natCast_isMaximal hp).eq_of_le (Ideal.IsPrime.under ℤ _).ne_top ?_).symm
  rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap, map_natCast]
  exact A.natCast_mem_primeBelow L hA

p2m_export "ValuationSubring" "under_int_primeBelow"
private theorem _root_.ValuationSubring.primeBelow_liesOver (hp : p.Prime) (hA : A.LiesOverPrime p) :
    (A.primeBelow L).LiesOver (Ideal.span {(p : ℤ)}) :=
  ⟨(A.under_int_primeBelow L hp hA).symm⟩

p2m_export "ValuationSubring" "primeBelow_liesOver"
private theorem _root_.ValuationSubring.isMaximal_primeBelow [FiniteDimensional ℚ L] (hp : p.Prime) (hA : A.LiesOverPrime p) :
    (A.primeBelow L).IsMaximal :=
  (A.primeBelow_isPrime L).isMaximal (A.primeBelow_ne_bot L hp hA)

p2m_export "ValuationSubring" "isMaximal_primeBelow"
end Integers
p2m_reactivate "P2MW.S_ValuationSubring_exists_ideal_ringOfIntegers_inertia_eq_map_restrictNormalHom.B6Inertia"

section Localization

variable (A : ValuationSubring (AlgebraicClosure ℚ)) (L : IntermediateField ℚ (AlgebraicClosure ℚ))
  {p : ℕ}

private def _root_.ValuationSubring.heightOneSpectrumBelow (hp : p.Prime) (hA : A.LiesOverPrime p) :
    IsDedekindDomain.HeightOneSpectrum (𝓞 L) :=
  ⟨A.primeBelow L, inferInstance, A.primeBelow_ne_bot L hp hA⟩

p2m_export "ValuationSubring" "heightOneSpectrumBelow"
@[scoped simp] theorem heightOneSpectrumBelow_asIdeal (hp : p.Prime) (hA : A.LiesOverPrime p) :
    (A.heightOneSpectrumBelow L hp hA).asIdeal = A.primeBelow L := rfl

variable [FiniteDimensional ℚ L]

private theorem _root_.ValuationSubring.exists_mul_eq_of_mem (hp : p.Prime) (hA : A.LiesOverPrime p) (z : L)
    (hz : algebraMap L (AlgebraicClosure ℚ) z ∈ A) :
    ∃ x s : 𝓞 L, s ∉ A.primeBelow L ∧ z * s = x := by
  obtain ⟨n, d, h | h⟩ :=
    (A.heightOneSpectrumBelow L hp hA).exists_primeCompl_mul_eq_or_mul_eq (K := L) z
  · exact ⟨n, d, d.2, h⟩
  · refine ⟨d, n, ?_, h⟩

    have hd : A.valuation (algebraMap L (AlgebraicClosure ℚ) ((d : 𝓞 L) : L)) = 1 :=
      (A.notMem_primeBelow_iff L).mp d.2
    rw [A.notMem_primeBelow_iff L]
    refine le_antisymm (A.valuation_algebraMap_ringOfIntegers_le_one L n) ?_
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

p2m_export "ValuationSubring" "exists_mul_eq_of_mem"

private theorem _root_.ValuationSubring.mem_of_adicValuation_le_one (hp : p.Prime) (hA : A.LiesOverPrime p) (z : L)
    (hz : (A.heightOneSpectrumBelow L hp hA).valuation L z ≤ 1) :
    algebraMap L (AlgebraicClosure ℚ) z ∈ A := by
  obtain ⟨n, d, h⟩ :=
    (A.heightOneSpectrumBelow L hp hA).exists_primeCompl_mul_eq_of_integer z hz
  have hd : A.valuation (algebraMap L (AlgebraicClosure ℚ) ((d : 𝓞 L) : L)) = 1 :=
    (A.notMem_primeBelow_iff L).mp d.2
  have key : A.valuation (algebraMap L (AlgebraicClosure ℚ) z) *
      A.valuation (algebraMap L (AlgebraicClosure ℚ) ((d : 𝓞 L) : L)) ≤ 1 := by
    rw [← map_mul, ← map_mul]
    change A.valuation (algebraMap L (AlgebraicClosure ℚ) (z * algebraMap (𝓞 L) L d)) ≤ 1
    rw [h]
    exact A.valuation_algebraMap_ringOfIntegers_le_one L n
  rw [hd, mul_one] at key
  exact (A.valuation_le_one_iff _).mp key

p2m_export "ValuationSubring" "mem_of_adicValuation_le_one"

private theorem _root_.ValuationSubring.isEquiv_valuation_comap_adicValuation (hp : p.Prime) (hA : A.LiesOverPrime p) :
    (A.valuation.comap (algebraMap L (AlgebraicClosure ℚ))).IsEquiv
      ((A.heightOneSpectrumBelow L hp hA).valuation L) := by
  refine Valuation.isEquiv_iff_val_le_one.mpr fun {z} => ?_
  rw [Valuation.comap_apply, valuation_le_one_iff]
  constructor
  · intro hz
    obtain ⟨x, s, hs, hzs⟩ := A.exists_mul_eq_of_mem L hp hA z hz
    have hs1 : (A.heightOneSpectrumBelow L hp hA).valuation L ((s : 𝓞 L) : L) = 1 :=
      (IsDedekindDomain.HeightOneSpectrum.valuation_eq_one_iff_notMem (K := L)
        (v := A.heightOneSpectrumBelow L hp hA)).mpr hs
    have h := congrArg ((A.heightOneSpectrumBelow L hp hA).valuation L) hzs
    rw [map_mul, hs1, mul_one] at h
    rw [h]
    exact (A.heightOneSpectrumBelow L hp hA).valuation_le_one (K := L) x
  · exact A.mem_of_adicValuation_le_one L hp hA z

p2m_export "ValuationSubring" "isEquiv_valuation_comap_adicValuation"
end Localization
p2m_reactivate "P2MW.S_ValuationSubring_exists_ideal_ringOfIntegers_inertia_eq_map_restrictNormalHom.B6Inertia"

section Ramification

variable (A : ValuationSubring (AlgebraicClosure ℚ)) (L : IntermediateField ℚ (AlgebraicClosure ℚ))
  [FiniteDimensional ℚ L] {p : ℕ}

omit [FiniteDimensional ℚ L] in
theorem map_span_natCast_eq :
    Ideal.map (algebraMap ℤ (𝓞 L)) (Ideal.span {(p : ℤ)}) = Ideal.span {(p : 𝓞 L)} := by
  rw [Ideal.map_span, Set.image_singleton, map_natCast]

private theorem _root_.ValuationSubring.adicValuation_natCast_eq_exp_neg_ramificationIdx (hp : p.Prime) (hA : A.LiesOverPrime p) :
    (A.heightOneSpectrumBelow L hp hA).valuation L (p : L) =
      WithZero.exp (-(Ideal.ramificationIdx' (Ideal.span {(p : ℤ)}) (A.primeBelow L) : ℤ)) := by
  classical
  have hp0 : (p : 𝓞 L) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hspan0 : Ideal.span {(p : 𝓞 L)} ≠ ⊥ := by
    simpa only [ne_eq, Ideal.span_singleton_eq_bot] using hp0
  have hmap0 : Ideal.map (algebraMap ℤ (𝓞 L)) (Ideal.span {(p : ℤ)}) ≠ ⊥ := by
    rwa [map_span_natCast_eq]
  rw [show (p : L) = algebraMap (𝓞 L) L (p : 𝓞 L) from (map_natCast _ p).symm,
    IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
    IsDedekindDomain.HeightOneSpectrum.intValuation_if_neg _ hp0, heightOneSpectrumBelow_asIdeal,
    Ideal.count_associates_factors_eq hspan0 (A.primeBelow_isPrime L)
      (A.primeBelow_ne_bot L hp hA),
    Ideal.IsDedekindDomain.ramificationIdx'_eq_normalizedFactors_count hmap0 (A.primeBelow_isPrime L)
      (A.primeBelow_ne_bot L hp hA), map_span_natCast_eq]

p2m_export "ValuationSubring" "adicValuation_natCast_eq_exp_neg_ramificationIdx"

private theorem _root_.ValuationSubring.dvd_ramificationIdx_of_valuation_pow_eq (hp : p.Prime) (hA : A.LiesOverPrime p)
    (z : L) {m a : ℕ} (hm : 0 < m) (hcop : Nat.Coprime a m)
    (hval : A.valuation (algebraMap L (AlgebraicClosure ℚ) z) ^ m =
      A.valuation (p : AlgebraicClosure ℚ) ^ a) :
    m ∣ Ideal.ramificationIdx' (Ideal.span {(p : ℤ)}) (A.primeBelow L) := by
  set e := Ideal.ramificationIdx' (Ideal.span {(p : ℤ)}) (A.primeBelow L) with he
  set w := (A.heightOneSpectrumBelow L hp hA).valuation L with hw
  have hequiv := A.isEquiv_valuation_comap_adicValuation L hp hA

  have hval' : w (z ^ m) = w ((p : L) ^ a) := by
    refine (hequiv.eq_iff).mp ?_
    simp only [Valuation.comap_apply, map_pow, map_natCast]
    exact hval
  rw [map_pow, map_pow, hw, A.adicValuation_natCast_eq_exp_neg_ramificationIdx L hp hA,
    ← he, ← WithZero.exp_nsmul] at hval'
  have hz0 : (A.heightOneSpectrumBelow L hp hA).valuation L z ≠ 0 := by
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

p2m_export "ValuationSubring" "dvd_ramificationIdx_of_valuation_pow_eq"
end Ramification
p2m_reactivate "P2MW.S_ValuationSubring_exists_ideal_ringOfIntegers_inertia_eq_map_restrictNormalHom.B6Inertia"

section General

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem valuation_sub_lt_one_of_mem_inertiaSubgroupIn' (A : ValuationSubring F) {σ : F ≃ₐ[K] F}
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
p2m_reactivate "P2MW.S_ValuationSubring_exists_ideal_ringOfIntegers_inertia_eq_map_restrictNormalHom.B6Inertia"

section Center

variable (A : ValuationSubring (AlgebraicClosure ℚ)) {p : ℕ}

private def _root_.ValuationSubring.integralClosureToValuationSubring : integralClosure ℤ (AlgebraicClosure ℚ) →+* A :=
  (integralClosure ℤ (AlgebraicClosure ℚ)).val.toRingHom.codRestrict A.toSubring
    A.coe_integralClosure_mem

p2m_export "ValuationSubring" "integralClosureToValuationSubring"

private def _root_.ValuationSubring.center : Ideal (integralClosure ℤ (AlgebraicClosure ℚ)) :=
  (IsLocalRing.maximalIdeal A).comap A.integralClosureToValuationSubring

p2m_export "ValuationSubring" "center"
private theorem _root_.ValuationSubring.mem_center_iff {b : integralClosure ℤ (AlgebraicClosure ℚ)} :
    b ∈ A.center ↔ A.valuation b < 1 := by
  rw [center, Ideal.mem_comap, valuation_lt_one_iff]
  rfl

p2m_export "ValuationSubring" "mem_center_iff"
scoped instance center_isPrime : A.center.IsPrime := Ideal.IsPrime.comap _

private theorem _root_.ValuationSubring.natCast_mem_center (hA : A.LiesOverPrime p) :
    (p : integralClosure ℤ (AlgebraicClosure ℚ)) ∈ A.center := by
  rw [mem_center_iff, ← mem_nonunits_iff]
  simpa using (show ((p : ℕ) : AlgebraicClosure ℚ) ∈ A.nonunits from hA)

p2m_export "ValuationSubring" "natCast_mem_center"
private theorem _root_.ValuationSubring.valuation_eq_one_of_notMem_center {s : integralClosure ℤ (AlgebraicClosure ℚ)}
    (hs : s ∉ A.center) : A.valuation s = 1 :=
  le_antisymm ((A.valuation_le_one_iff _).mpr (A.coe_integralClosure_mem s))
    (not_lt.mp fun h => hs (A.mem_center_iff.mpr h))

p2m_export "ValuationSubring" "valuation_eq_one_of_notMem_center"

theorem mem_primeBelow_iff_mem_center (L : IntermediateField ℚ (AlgebraicClosure ℚ)) (x : 𝓞 L) :
    x ∈ A.primeBelow L ↔
      (⟨algebraMap L (AlgebraicClosure ℚ) (x : L), map_isIntegral_int _
        (NumberField.RingOfIntegers.isIntegral_coe x)⟩ :
          integralClosure ℤ (AlgebraicClosure ℚ)) ∈ A.center := by
  rw [mem_primeBelow_iff, mem_center_iff]

private theorem _root_.ValuationSubring.exists_integralClosure_mul_eq_of_mem (hp : p.Prime) (hA : A.LiesOverPrime p)
    (a : AlgebraicClosure ℚ) (ha : a ∈ A) :
    ∃ x s : integralClosure ℤ (AlgebraicClosure ℚ), s ∉ A.center ∧
      a * s = x := by
  let F : IntermediateField ℚ (AlgebraicClosure ℚ) := IntermediateField.adjoin ℚ {a}
  haveI : FiniteDimensional ℚ F :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral a)
  let a' : F := ⟨a, IntermediateField.mem_adjoin_simple_self ℚ a⟩
  have ha' : algebraMap F (AlgebraicClosure ℚ) a' = a := rfl
  obtain ⟨x, s, hs, hxs⟩ := A.exists_mul_eq_of_mem F hp hA a' (ha'.symm ▸ ha)
  refine ⟨⟨algebraMap F (AlgebraicClosure ℚ) (x : F), map_isIntegral_int _
      (NumberField.RingOfIntegers.isIntegral_coe x)⟩,
    ⟨algebraMap F (AlgebraicClosure ℚ) (s : F), map_isIntegral_int _
      (NumberField.RingOfIntegers.isIntegral_coe s)⟩, ?_, ?_⟩
  · rwa [← mem_primeBelow_iff_mem_center]
  · change a * algebraMap F (AlgebraicClosure ℚ) (s : F) = algebraMap F (AlgebraicClosure ℚ) (x : F)
    rw [← ha', ← map_mul, hxs]

p2m_export "ValuationSubring" "exists_integralClosure_mul_eq_of_mem"

private theorem _root_.ValuationSubring.apply_mem_and_valuation_sub_lt_one (hp : p.Prime) (hA : A.LiesOverPrime p)
    (ρ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (hρ : ∀ b : integralClosure ℤ (AlgebraicClosure ℚ),
      A.valuation (ρ b - b) < 1)
    (a : AlgebraicClosure ℚ) (ha : a ∈ A) : ρ a ∈ A ∧ A.valuation (ρ a - a) < 1 := by
  obtain ⟨x, s, hs, hax⟩ := A.exists_integralClosure_mul_eq_of_mem hp hA a ha
  have hvs : A.valuation (s : AlgebraicClosure ℚ) = 1 := A.valuation_eq_one_of_notMem_center hs
  have hvx : A.valuation (x : AlgebraicClosure ℚ) ≤ 1 :=
    (A.valuation_le_one_iff _).mpr (A.coe_integralClosure_mem x)
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

p2m_export "ValuationSubring" "apply_mem_and_valuation_sub_lt_one"

private theorem _root_.ValuationSubring.mem_inertiaSubgroupIn_of_forall_valuation_sub_lt_one (hp : p.Prime)
    (hA : A.LiesOverPrime p) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (hσ : ∀ b : integralClosure ℤ (AlgebraicClosure ℚ), A.valuation (σ b - b) < 1) :
    σ ∈ A.inertiaSubgroupIn ℚ := by
  have key := A.apply_mem_and_valuation_sub_lt_one hp hA

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

p2m_export "ValuationSubring" "mem_inertiaSubgroupIn_of_forall_valuation_sub_lt_one"
end Center
p2m_reactivate "P2MW.S_ValuationSubring_exists_ideal_ringOfIntegers_inertia_eq_map_restrictNormalHom.B6Inertia"

section Lift

variable (A : ValuationSubring (AlgebraicClosure ℚ)) (L : IntermediateField ℚ (AlgebraicClosure ℚ))
  {p : ℕ}

theorem algebraMap_restrictNormalHom_apply [Normal ℚ L]
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : L) :
    algebraMap L (AlgebraicClosure ℚ) (AlgEquiv.restrictNormalHom L σ x) =
      σ (algebraMap L (AlgebraicClosure ℚ) x) :=
  AlgEquiv.restrictNormal_commutes σ L x

variable [IsGalois ℚ L]

private theorem _root_.ValuationSubring.exists_lift_valuation_sub_lt_one_of_mem_inertia (τ : L ≃ₐ[ℚ] L)
    (hτ : τ ∈ (A.primeBelow L).inertia (L ≃ₐ[ℚ] L)) :
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
  set Q : Ideal (𝓞 L) := A.primeBelow L with hQdef
  set 𝔔 : Ideal (integralClosure ℤ (AlgebraicClosure ℚ)) := A.center with h𝔔def
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
    exact A.mem_center_iff.mp h2

p2m_export "ValuationSubring" "exists_lift_valuation_sub_lt_one_of_mem_inertia"

private theorem _root_.ValuationSubring.exists_mem_inertiaSubgroupIn_restrictNormalHom_eq (hp : p.Prime) (hA : A.LiesOverPrime p)
    (τ : L ≃ₐ[ℚ] L) (hτ : τ ∈ (A.primeBelow L).inertia (L ≃ₐ[ℚ] L)) :
    ∃ σ ∈ A.inertiaSubgroupIn ℚ, AlgEquiv.restrictNormalHom L σ = τ := by
  obtain ⟨σ, hσL, hσ⟩ := A.exists_lift_valuation_sub_lt_one_of_mem_inertia L τ hτ
  exact ⟨σ, A.mem_inertiaSubgroupIn_of_forall_valuation_sub_lt_one hp hA σ hσ, hσL⟩

p2m_export "ValuationSubring" "exists_mem_inertiaSubgroupIn_restrictNormalHom_eq"
end Lift
p2m_reactivate "P2MW.S_ValuationSubring_exists_ideal_ringOfIntegers_inertia_eq_map_restrictNormalHom.B6Inertia"

section Dictionary

variable (A : ValuationSubring (AlgebraicClosure ℚ)) (L : IntermediateField ℚ (AlgebraicClosure ℚ))
  {p : ℕ}

theorem coe_smul_ringOfIntegers (τ : L ≃ₐ[ℚ] L) (x : 𝓞 L) : ((τ • x : 𝓞 L) : L) = τ (x : L) :=
  rfl

variable [IsGalois ℚ L]

private theorem _root_.ValuationSubring.map_restrictNormalHom_inertiaSubgroupIn_le :
    (A.inertiaSubgroupIn ℚ).map (AlgEquiv.restrictNormalHom L) ≤
      (A.primeBelow L).inertia (L ≃ₐ[ℚ] L) := by
  rintro _ ⟨σ, hσ, rfl⟩
  refine AddSubgroup.mem_inertia.mpr fun x => ?_
  change AlgEquiv.restrictNormalHom L σ • x - x ∈ A.primeBelow L
  rw [mem_primeBelow_iff]
  have hcoe : (((AlgEquiv.restrictNormalHom L σ • x - x : 𝓞 L)) : L) =
      AlgEquiv.restrictNormalHom L σ (x : L) - x := rfl
  rw [hcoe, map_sub, algebraMap_restrictNormalHom_apply]
  exact (valuation_sub_lt_one_of_mem_inertiaSubgroupIn' A hσ
    (A.algebraMap_ringOfIntegers_mem L x)).2

p2m_export "ValuationSubring" "map_restrictNormalHom_inertiaSubgroupIn_le"

private theorem _root_.ValuationSubring.map_restrictNormalHom_inertiaSubgroupIn_eq_inertia (hp : p.Prime) (hA : A.LiesOverPrime p) :
    (A.inertiaSubgroupIn ℚ).map (AlgEquiv.restrictNormalHom L) =
      (A.primeBelow L).inertia (L ≃ₐ[ℚ] L) := by
  refine le_antisymm (A.map_restrictNormalHom_inertiaSubgroupIn_le L) fun τ hτ => ?_
  obtain ⟨σ, hσ, rfl⟩ := A.exists_mem_inertiaSubgroupIn_restrictNormalHom_eq L hp hA τ hτ
  exact Subgroup.mem_map_of_mem _ hσ

p2m_export "ValuationSubring" "map_restrictNormalHom_inertiaSubgroupIn_eq_inertia"
variable [FiniteDimensional ℚ L]

attribute [local instance] Ideal.Quotient.field in

private theorem _root_.ValuationSubring.card_inertia_primeBelow_eq_ramificationIdx (hp : p.Prime) (hA : A.LiesOverPrime p) :
    Nat.card ((A.primeBelow L).inertia (L ≃ₐ[ℚ] L)) =
      Ideal.ramificationIdx' (Ideal.span {(p : ℤ)}) (A.primeBelow L) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI := A.primeBelow_liesOver L hp hA
  haveI := A.isMaximal_primeBelow L hp hA
  rw [Ideal.card_inertia_eq_ramificationIdxIn (G := L ≃ₐ[ℚ] L) (Ideal.span {(p : ℤ)}) (A.primeBelow L),
    Ideal.ramificationIdxIn_eq_ramificationIdx (Ideal.span {(p : ℤ)}) (A.primeBelow L)
      (L ≃ₐ[ℚ] L)]
  exact (Ideal.ramificationIdx'_eq_ramificationIdx (p := Ideal.span {(p : ℤ)}) (A.primeBelow L)
    (by simpa [Ideal.span_singleton_eq_bot] using hp.ne_zero)).symm

p2m_export "ValuationSubring" "card_inertia_primeBelow_eq_ramificationIdx"

private theorem _root_.ValuationSubring.card_map_restrictNormalHom_inertiaSubgroupIn (hp : p.Prime) (hA : A.LiesOverPrime p) :
    Nat.card ((A.inertiaSubgroupIn ℚ).map (AlgEquiv.restrictNormalHom L)) =
      Ideal.ramificationIdx' (Ideal.span {(p : ℤ)}) (A.primeBelow L) := by
  rw [A.map_restrictNormalHom_inertiaSubgroupIn_eq_inertia L hp hA,
    A.card_inertia_primeBelow_eq_ramificationIdx L hp hA]

p2m_export "ValuationSubring" "card_map_restrictNormalHom_inertiaSubgroupIn"
omit [IsGalois ℚ L] in

theorem ramificationIdx_primeBelow_ne_zero (hp : p.Prime) (hA : A.LiesOverPrime p) :
    Ideal.ramificationIdx' (Ideal.span {(p : ℤ)}) (A.primeBelow L) ≠ 0 :=
  haveI := A.primeBelow_liesOver L hp hA
  Ideal.IsDedekindDomain.ramificationIdx_ne_zero_of_liesOver _
    (by simpa [Ideal.span_singleton_eq_bot] using hp.ne_zero)

theorem dvd_card_map_restrictNormalHom_inertiaSubgroupIn (hp : p.Prime) (hA : A.LiesOverPrime p)
    (z : L) {m a : ℕ} (hm : 0 < m) (hcop : Nat.Coprime a m)
    (hval : A.valuation (algebraMap L (AlgebraicClosure ℚ) z) ^ m =
      A.valuation (p : AlgebraicClosure ℚ) ^ a) :
    m ∣ Nat.card ((A.inertiaSubgroupIn ℚ).map (AlgEquiv.restrictNormalHom L)) := by
  rw [A.card_map_restrictNormalHom_inertiaSubgroupIn L hp hA]
  exact A.dvd_ramificationIdx_of_valuation_pow_eq L hp hA z hm hcop hval

private theorem _root_.ValuationSubring.map_restrictNormalHom_inertiaSubgroupIn_eq_bot_iff (hp : p.Prime) (hA : A.LiesOverPrime p) :
    (A.inertiaSubgroupIn ℚ).map (AlgEquiv.restrictNormalHom L) = ⊥ ↔
      Ideal.ramificationIdx' (Ideal.span {(p : ℤ)}) (A.primeBelow L) = 1 := by
  rw [← Subgroup.card_eq_one, A.card_map_restrictNormalHom_inertiaSubgroupIn L hp hA]

p2m_export "ValuationSubring" "map_restrictNormalHom_inertiaSubgroupIn_eq_bot_iff"
omit [IsGalois ℚ L] in

private theorem _root_.ValuationSubring.ramificationIdx_primeBelow_eq_one_iff_isUnramifiedAt (hp : p.Prime)
    (hA : A.LiesOverPrime p) :
    Ideal.ramificationIdx' (Ideal.span {(p : ℤ)}) (A.primeBelow L) = 1 ↔
      Algebra.IsUnramifiedAt ℤ (A.primeBelow L) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI := A.primeBelow_liesOver L hp hA
  have e := Ideal.ramificationIdx'_eq_ramificationIdx (p := Ideal.span {(p : ℤ)}) (A.primeBelow L)
    (by simpa [Ideal.span_singleton_eq_bot] using hp.ne_zero)
  rw [e, Algebra.isUnramifiedAt_iff_of_isDedekindDomain]

p2m_export "ValuationSubring" "ramificationIdx_primeBelow_eq_one_iff_isUnramifiedAt"

theorem map_restrictNormalHom_inertiaSubgroupIn_eq_bot_iff_isUnramifiedAt (hp : p.Prime)
    (hA : A.LiesOverPrime p) :
    (A.inertiaSubgroupIn ℚ).map (AlgEquiv.restrictNormalHom L) = ⊥ ↔
      Algebra.IsUnramifiedAt ℤ (A.primeBelow L) := by
  rw [A.map_restrictNormalHom_inertiaSubgroupIn_eq_bot_iff L hp hA,
    A.ramificationIdx_primeBelow_eq_one_iff_isUnramifiedAt L hp hA]

end Dictionary
p2m_reactivate "P2MW.S_ValuationSubring_exists_ideal_ringOfIntegers_inertia_eq_map_restrictNormalHom.B6Inertia"

section Extension

variable (L : IntermediateField ℚ (AlgebraicClosure ℚ)) {p : ℕ}

theorem exists_liesOverPrime_primeBelow_eq (𝔔 : Ideal (𝓞 L)) [h𝔔 : 𝔔.IsMaximal]
    (hp𝔔 : (p : 𝓞 L) ∈ 𝔔) :
    ∃ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p ∧ A.primeBelow L = 𝔔 := by

  let g : 𝓞 L →+* AlgebraicClosure ℚ :=
    (algebraMap L (AlgebraicClosure ℚ)).comp (algebraMap (𝓞 L) L)
  let e : 𝓞 L →+* g.range := g.rangeRestrict
  have he : Function.Surjective e := g.rangeRestrict_surjective
  have hg_inj : Function.Injective g := fun x y h =>
    NumberField.RingOfIntegers.coe_injective ((algebraMap L (AlgebraicClosure ℚ)).injective h)
  have he_inj : Function.Injective e := fun x y hxy => hg_inj (congrArg Subtype.val hxy :)
  let I : Ideal g.range := 𝔔.map e
  have hIcomap : I.comap e = 𝔔 := by
    rw [Ideal.comap_map_of_surjective e he, Ideal.comap_bot_of_injective e he_inj, sup_bot_eq]
  have hI : I ≠ ⊤ := fun htop => h𝔔.ne_top (by rw [← hIcomap, htop, Ideal.comap_top])
  obtain ⟨A, hSA, hIA⟩ := Ideal.image_subset_nonunits_valuationSubring (A := g.range) I hI
  have hle : 𝔔 ≤ A.primeBelow L := by
    intro x hx
    rw [mem_primeBelow_iff_mem_nonunits]
    exact hIA ⟨e x, Ideal.mem_map_of_mem e hx, rfl⟩
  have heq : A.primeBelow L = 𝔔 := (h𝔔.eq_of_le (A.primeBelow_isPrime L).ne_top hle).symm
  refine ⟨A, ?_, heq⟩
  have := hle hp𝔔
  rw [mem_primeBelow_iff_mem_nonunits] at this
  change algebraMap L (AlgebraicClosure ℚ) (algebraMap (𝓞 L) L (p : 𝓞 L)) ∈ A.nonunits at this
  rwa [map_natCast, map_natCast] at this

end Extension
p2m_reactivate "P2MW.S_ValuationSubring_exists_ideal_ringOfIntegers_inertia_eq_map_restrictNormalHom.B6Inertia"

section Cyclotomic

variable (A : ValuationSubring (AlgebraicClosure ℚ)) (L : IntermediateField ℚ (AlgebraicClosure ℚ))
  {p : ℕ}

private theorem _root_.ValuationSubring.map_restrictNormalHom_inertiaSubgroupIn_eq_top_of_isCyclotomicExtension
    [FiniteDimensional ℚ L] [IsGalois ℚ L] [IsCyclotomicExtension {p} ℚ L]
    (hp : p.Prime) (hA : A.LiesOverPrime p) :
    (A.inertiaSubgroupIn ℚ).map (AlgEquiv.restrictNormalHom L) = ⊤ := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI := A.primeBelow_liesOver L hp hA
  refine Subgroup.eq_top_of_card_eq _ ?_
  have e := Ideal.ramificationIdx'_eq_ramificationIdx (p := Ideal.span {(p : ℤ)}) (A.primeBelow L)
    (by simpa [Ideal.span_singleton_eq_bot] using hp.ne_zero)
  rw [A.card_map_restrictNormalHom_inertiaSubgroupIn L hp hA, e,
    IsCyclotomicExtension.Rat.ramificationIdx_eq_of_prime p L (A.primeBelow L),
    IsGalois.card_aut_eq_finrank,
    IsCyclotomicExtension.finrank (K := ℚ) (n := p) L
      (Polynomial.cyclotomic.irreducible_rat hp.pos),
    Nat.totient_prime hp]

p2m_export "ValuationSubring" "map_restrictNormalHom_inertiaSubgroupIn_eq_top_of_isCyclotomicExtension"

theorem exists_mem_inertiaSubgroupIn_cyclotomic_character (hp : p.Prime) (hA : A.LiesOverPrime p)
    (a : (ZMod p)ˣ) :
    ∃ σ ∈ A.inertiaSubgroupIn ℚ, ∀ μ : AlgebraicClosure ℚ, μ ^ p = 1 →
      σ μ = μ ^ (a : ZMod p).val := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩

  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure ℚ) p
  let L : IntermediateField ℚ (AlgebraicClosure ℚ) := IntermediateField.adjoin ℚ {ζ}
  haveI : FiniteDimensional ℚ L :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral ζ)
  haveI : IsCyclotomicExtension {p} ℚ L := hζ.intermediateField_adjoin_isCyclotomicExtension ℚ
  haveI : IsGalois ℚ L := IsCyclotomicExtension.isGalois {p} ℚ L
  let ζL : L := ⟨ζ, IntermediateField.mem_adjoin_simple_self ℚ ζ⟩
  have hζL : IsPrimitiveRoot ζL p :=
    IsPrimitiveRoot.of_map_of_injective (f := algebraMap L (AlgebraicClosure ℚ)) hζ
      (algebraMap L (AlgebraicClosure ℚ)).injective

  let χ := hζL.autToPow ℚ
  have hχ : Function.Bijective χ := by
    refine (Nat.bijective_iff_injective_and_card χ).mpr ⟨hζL.autToPow_injective ℚ, ?_⟩
    rw [IsGalois.card_aut_eq_finrank,
      IsCyclotomicExtension.finrank (K := ℚ) (n := p) L
        (Polynomial.cyclotomic.irreducible_rat hp.pos),
      Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
  obtain ⟨τ, hτ⟩ := hχ.2 a
  have hτζ : τ ζL = ζL ^ (a : ZMod p).val := by
    rw [← hτ]
    exact (hζL.autToPow_spec ℚ τ).symm

  have hτmem : τ ∈ (A.inertiaSubgroupIn ℚ).map (AlgEquiv.restrictNormalHom L) := by
    rw [A.map_restrictNormalHom_inertiaSubgroupIn_eq_top_of_isCyclotomicExtension L hp hA]
    exact Subgroup.mem_top τ
  obtain ⟨σ, hσ, hσL⟩ := Subgroup.mem_map.mp hτmem
  refine ⟨σ, hσ, fun μ hμ => ?_⟩
  have hσζ : σ ζ = ζ ^ (a : ZMod p).val := by
    change σ (algebraMap L (AlgebraicClosure ℚ) ζL) = (algebraMap L (AlgebraicClosure ℚ) ζL) ^ _
    rw [← algebraMap_restrictNormalHom_apply, hσL, hτζ, map_pow]
  obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hμ
  rw [map_pow, hσζ, ← pow_mul, ← pow_mul, mul_comm]

end Cyclotomic
p2m_reactivate "P2MW.S_ValuationSubring_exists_ideal_ringOfIntegers_inertia_eq_map_restrictNormalHom.B6Inertia"

section Transitivity

variable {p : ℕ}

theorem mem_nonunits_iff_mem_and {K : Type*} [Field K] (B : ValuationSubring K) (x : K) :
    x ∈ B.nonunits ↔ x ∈ B ∧ (x = 0 ∨ x⁻¹ ∉ B) := by
  rw [mem_nonunits_iff]
  constructor
  · intro hx
    refine ⟨(B.valuation_le_one_iff x).mp hx.le, ?_⟩
    rcases eq_or_ne x 0 with h0 | h0
    · exact Or.inl h0
    · right
      rw [← B.valuation_le_one_iff, not_le]
      exact (B.valuation.val_lt_one_iff h0).mp hx
  · rintro ⟨hxB, h0 | hinv⟩
    · rw [h0, map_zero]; exact zero_lt_one
    · have hx0 : x ≠ 0 := by rintro rfl; exact hinv (by rw [inv_zero]; exact B.zero_mem)
      rw [← B.valuation_le_one_iff, not_le] at hinv
      exact (B.valuation.val_lt_one_iff hx0).mpr hinv

theorem mem_nonunits_pointwise_smul_iff {K F : Type*} [Field K] [Field F] [Algebra K F]
    (g : F ≃ₐ[K] F) (B : ValuationSubring F) (x : F) :
    x ∈ (g • B).nonunits ↔ g⁻¹ x ∈ B.nonunits := by
  rw [mem_nonunits_iff_mem_and, mem_nonunits_iff_mem_and, mem_pointwise_smul_iff_inv_smul_mem,
    mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def, AlgEquiv.smul_def, map_inv₀,
    map_eq_zero_iff _ g⁻¹.injective]

variable (A A' : ValuationSubring (AlgebraicClosure ℚ))

private theorem _root_.ValuationSubring.liesOverPrime_pointwise_smul_iff (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    (g • A).LiesOverPrime p ↔ A.LiesOverPrime p := by
  rw [LiesOverPrime, LiesOverPrime, mem_nonunits_pointwise_smul_iff, map_natCast]

p2m_export "ValuationSubring" "liesOverPrime_pointwise_smul_iff"

theorem center_pointwise_smul (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    (g • A).center = g • A.center := by
  ext b
  rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem, mem_center_iff, mem_center_iff,
    ← mem_nonunits_iff, ← mem_nonunits_iff, mem_nonunits_pointwise_smul_iff]
  rfl

theorem le_of_center_le (hp : p.Prime) (hA : A.LiesOverPrime p) (h : A'.center ≤ A.center) :
    A ≤ A' := by
  intro a ha
  obtain ⟨x, s, hs, hax⟩ := A.exists_integralClosure_mul_eq_of_mem hp hA a ha
  have hvs : A'.valuation (s : AlgebraicClosure ℚ) = 1 :=
    A'.valuation_eq_one_of_notMem_center fun h' => hs (h h')
  have hs0 : (s : AlgebraicClosure ℚ) ≠ 0 := fun h0 => by
    rw [h0, map_zero] at hvs; exact zero_ne_one hvs
  rw [← A'.valuation_le_one_iff, (eq_div_iff hs0).mpr hax, map_div₀, hvs, div_one]
  exact (A'.valuation_le_one_iff _).mpr (A'.coe_integralClosure_mem x)

theorem eq_of_center_eq (hp : p.Prime) (hA : A.LiesOverPrime p) (hA' : A'.LiesOverPrime p)
    (h : A.center = A'.center) : A = A' :=
  le_antisymm (le_of_center_le A A' hp hA h.ge) (le_of_center_le A' A hp hA' h.le)

private theorem _root_.ValuationSubring.under_int_center (hp : p.Prime) (hA : A.LiesOverPrime p) :
    A.center.under ℤ = Ideal.span {(p : ℤ)} := by
  refine ((span_natCast_isMaximal hp).eq_of_le (Ideal.IsPrime.under ℤ _).ne_top ?_).symm
  rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap, map_natCast]
  exact A.natCast_mem_center hA

p2m_export "ValuationSubring" "under_int_center"

theorem exists_algEquiv_smul_eq_of_liesOverPrime' (hp : p.Prime) (hA : A.LiesOverPrime p)
    (hA' : A'.LiesOverPrime p) :
    ∃ g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, g • A = A' := by
  classical
  letI : TopologicalSpace (integralClosure ℤ (AlgebraicClosure ℚ)) := ⊥
  haveI : DiscreteTopology (integralClosure ℤ (AlgebraicClosure ℚ)) := ⟨rfl⟩
  haveI : ContinuousSMul (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      (integralClosure ℤ (AlgebraicClosure ℚ)) := by
    refine continuousSMul_iff_stabilizer_isOpen.mpr fun b => ?_
    haveI : FiniteDimensional ℚ (IntermediateField.adjoin ℚ {(b : AlgebraicClosure ℚ)}) :=
      IntermediateField.adjoin.finiteDimensional
        (Algebra.IsIntegral.isIntegral (b : AlgebraicClosure ℚ))
    refine Subgroup.isOpen_mono ?_
      (IntermediateField.fixingSubgroup_isOpen
        (IntermediateField.adjoin ℚ {(b : AlgebraicClosure ℚ)}))
    intro g hg
    rw [MulAction.mem_stabilizer_iff]
    apply Subtype.ext
    change g (b : AlgebraicClosure ℚ) = b
    rw [IntermediateField.mem_fixingSubgroup_iff] at hg
    exact hg _ (IntermediateField.mem_adjoin_simple_self ℚ (b : AlgebraicClosure ℚ))
  haveI : Algebra.IsInvariant ℤ (integralClosure ℤ (AlgebraicClosure ℚ))
      (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) := ⟨fun b hb => by
    have hb' : (b : AlgebraicClosure ℚ) ∈ Set.range (algebraMap ℚ (AlgebraicClosure ℚ)) := by
      rw [InfiniteGalois.mem_range_algebraMap_iff_fixed]
      intro g
      exact congrArg (fun z : integralClosure ℤ (AlgebraicClosure ℚ) => (z : AlgebraicClosure ℚ))
        (hb g)
    obtain ⟨y, hy⟩ := hb'
    have hyint : IsIntegral ℤ y := by
      obtain ⟨q, hq, hq0⟩ := (b.2 : IsIntegral ℤ (b : AlgebraicClosure ℚ))
      refine ⟨q, hq, (algebraMap ℚ (AlgebraicClosure ℚ)).injective ?_⟩
      rw [Polynomial.hom_eval₂, map_zero, hy]
      convert hq0 using 2 <;> first | rfl | exact Subsingleton.elim _ _
    obtain ⟨z, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.mp hyint
    refine ⟨z, Subtype.ext ?_⟩
    rw [← hy]
    change algebraMap ℤ (AlgebraicClosure ℚ) z =
      algebraMap ℚ (AlgebraicClosure ℚ) (algebraMap ℤ ℚ z)
    exact (IsScalarTower.algebraMap_apply ℤ ℚ (AlgebraicClosure ℚ) z)⟩
  have hunder : A.center.under ℤ = A'.center.under ℤ := by
    rw [A.under_int_center hp hA, A'.under_int_center hp hA']
  obtain ⟨g, hg⟩ := Algebra.IsInvariant.exists_smul_of_under_eq_of_profinite (A := ℤ)
    (G := AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) A.center A'.center hunder
  refine ⟨g, eq_of_center_eq _ _ hp ((A.liesOverPrime_pointwise_smul_iff g).mpr hA) hA' ?_⟩
  rw [center_pointwise_smul, ← hg]

end Transitivity
p2m_reactivate "P2MW.S_ValuationSubring_exists_ideal_ringOfIntegers_inertia_eq_map_restrictNormalHom.B6Inertia"

end ValuationSubring
p2m_reactivate "P2MW.S_ValuationSubring_exists_ideal_ringOfIntegers_inertia_eq_map_restrictNormalHom.B6Inertia P2MW.S_ValuationSubring_exists_ideal_ringOfIntegers_inertia_eq_map_restrictNormalHom.ValuationSubring"

end
p2m_reactivate "P2MW.S_ValuationSubring_exists_ideal_ringOfIntegers_inertia_eq_map_restrictNormalHom.B6Inertia P2MW.S_ValuationSubring_exists_ideal_ringOfIntegers_inertia_eq_map_restrictNormalHom.ValuationSubring"

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped NumberField Pointwise
open IsDedekindDomain

universe u v

namespace GaloisRep
namespace TameKernel

section Core
variable {B : Type u} [CommRing B] {G : Type v} [Group G] [MulSemiringAction G B]

theorem smul_mem_of_mem_inertia (𝔓 : Ideal B) {σ : G} (hσ : σ ∈ 𝔓.inertia G) {z : B} (hz : z ∈ 𝔓) : σ • z ∈ 𝔓 := by
  have h : σ • z - z ∈ 𝔓 := hσ z
  have : σ • z = (σ • z - z) + z := by ring
  rw [this]; exact 𝔓.add_mem h hz

theorem smul_mem_sq_of_mem_inertia (𝔓 : Ideal B) {σ : G} (hσ : σ ∈ 𝔓.inertia G) {z : B} (hz : z ∈ 𝔓 ^ 2) :
    σ • z ∈ 𝔓 ^ 2 := by

  let f : B →+* B := MulSemiringAction.toRingHom G B σ
  have hmap : 𝔓.map f ≤ 𝔓 := by
    rw [Ideal.map_le_iff_le_comap]
    intro z hz'
    exact smul_mem_of_mem_inertia 𝔓 hσ hz'
  have h2 : (𝔓 ^ 2).map f ≤ 𝔓 ^ 2 := by
    rw [Ideal.map_pow]; exact Ideal.pow_right_mono hmap 2
  exact h2 (Ideal.mem_map_of_mem f hz)

theorem pow_sub_pow_mem_sq (𝔓 : Ideal B) {a b : B} (hab : a - b ∈ 𝔓) {N : ℕ} (hN : (N : B) ∈ 𝔓) (hN0 : N ≠ 0) :
    a ^ N - b ^ N ∈ 𝔓 ^ 2 := by
  set m := a - b with hm
  have ha : a = b + m := by rw [hm]; ring
  rw [ha, add_pow, Finset.sum_range_succ, Nat.sub_self, pow_zero, mul_one, Nat.choose_self, Nat.cast_one, mul_one,
    add_sub_cancel_right]
  refine Ideal.sum_mem _ fun k hk => ?_
  rw [Finset.mem_range] at hk
  rcases Nat.lt_or_ge (N - k) 2 with hlt | hge
  ·
    have hk1 : N - k = 1 := by omega
    have hkN : k = N - 1 := by omega
    have hch : (N.choose k : B) = N := by
      rw [hkN, Nat.choose_symm (by omega : 1 ≤ N), Nat.choose_one_right]
    rw [hk1, pow_one, hch, pow_two]
    exact Ideal.mul_mem_mul (Ideal.mul_mem_left _ _ hab) hN
  ·
    have : m ^ (N - k) ∈ 𝔓 ^ 2 := by
      obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le hge
      rw [hj, pow_add]
      exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hab 2)
    exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ this)

theorem smul_sub_mem_sq_of_mem_inertia (𝔓 : Ideal B) [𝔓.IsMaximal] [Finite (B ⧸ 𝔓)]
    {ϖ : B} (hϖP : ϖ ∈ 𝔓) (hϖ : ∀ x ∈ 𝔓, ∃ y : B, x - ϖ * y ∈ 𝔓 ^ 2)
    {σ : G} (hσ : σ ∈ 𝔓.inertia G) (hσϖ : σ • ϖ - ϖ ∈ 𝔓 ^ 2) (x : B) :
    σ • x - x ∈ 𝔓 ^ 2 := by
  classical
  letI : Field (B ⧸ 𝔓) := Ideal.Quotient.field 𝔓
  letI : Fintype (B ⧸ 𝔓) := Fintype.ofFinite _
  set N := Fintype.card (B ⧸ 𝔓) with hNdef

  have hN : (N : B) ∈ 𝔓 := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast, hNdef]
    exact Nat.cast_card_eq_zero (B ⧸ 𝔓)
  have hN0 : N ≠ 0 := Fintype.card_ne_zero

  have hF : x ^ N - x ∈ 𝔓 := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow, hNdef, FiniteField.pow_card, sub_self]

  obtain ⟨y, hy⟩ := hϖ (x - x ^ N) (by rw [← neg_sub]; exact 𝔓.neg_mem hF)
  set e := x - x ^ N - ϖ * y with he
  have hx : x = x ^ N + ϖ * y + e := by rw [he]; ring

  have h1 : σ • (x ^ N) - x ^ N ∈ 𝔓 ^ 2 := by
    rw [smul_pow']
    exact pow_sub_pow_mem_sq 𝔓 (hσ x) hN hN0
  have h2 : σ • (ϖ * y) - ϖ * y ∈ 𝔓 ^ 2 := by
    have : σ • (ϖ * y) - ϖ * y = (σ • ϖ - ϖ) * (σ • y) + ϖ * (σ • y - y) := by
      rw [smul_mul']; ring
    rw [this]
    refine 𝔓 ^ 2 |>.add_mem (Ideal.mul_mem_right _ _ hσϖ) ?_
    rw [pow_two]
    exact Ideal.mul_mem_mul hϖP (hσ y)
  have h3 : σ • e - e ∈ 𝔓 ^ 2 := (𝔓 ^ 2).sub_mem (smul_mem_sq_of_mem_inertia 𝔓 hσ hy) hy
  have : σ • x - x = (σ • (x ^ N) - x ^ N) + (σ • (ϖ * y) - ϖ * y) + (σ • e - e) := by
    conv_lhs => rw [hx]
    rw [smul_add, smul_add]; ring
  rw [this]
  exact (𝔓 ^ 2).add_mem ((𝔓 ^ 2).add_mem h1 h2) h3

end Core
p2m_reactivate "P2MW.S_ValuationSubring_exists_ideal_ringOfIntegers_inertia_eq_map_restrictNormalHom.B6Inertia P2MW.S_ValuationSubring_exists_ideal_ringOfIntegers_inertia_eq_map_restrictNormalHom.ValuationSubring"

section TameChar
variable {B : Type u} [CommRing B] {G : Type v} [Group G] [MulSemiringAction G B]
variable (𝔓 : Ideal B) [𝔓.IsMaximal]
variable {ϖ : B}

theorem exists_tameCoeff (hϖP : ϖ ∈ 𝔓) (hgen : ∀ x ∈ 𝔓, ∃ y : B, x - ϖ * y ∈ 𝔓 ^ 2) {σ : G} (hσ : σ ∈ 𝔓.inertia G) : ∃ t : B, σ • ϖ - ϖ * t ∈ 𝔓 ^ 2 :=
  hgen (σ • ϖ) (smul_mem_of_mem_inertia 𝔓 hσ hϖP)

noncomputable def tameCoeff (hϖP : ϖ ∈ 𝔓) (hgen : ∀ x ∈ 𝔓, ∃ y : B, x - ϖ * y ∈ 𝔓 ^ 2) {σ : G} (hσ : σ ∈ 𝔓.inertia G) : B := (exists_tameCoeff 𝔓 hϖP hgen hσ).choose

theorem tameCoeff_spec (hϖP : ϖ ∈ 𝔓) (hgen : ∀ x ∈ 𝔓, ∃ y : B, x - ϖ * y ∈ 𝔓 ^ 2) {σ : G} (hσ : σ ∈ 𝔓.inertia G) : σ • ϖ - ϖ * tameCoeff 𝔓 hϖP hgen hσ ∈ 𝔓 ^ 2 :=
  (exists_tameCoeff 𝔓 hϖP hgen hσ).choose_spec

theorem tameCoeff_unique (hreg : ∀ c : B, c * ϖ ∈ 𝔓 ^ 2 → c ∈ 𝔓) {z t t' : B} (ht : z - ϖ * t ∈ 𝔓 ^ 2) (ht' : z - ϖ * t' ∈ 𝔓 ^ 2) : t - t' ∈ 𝔓 := by
  apply hreg
  have : (t - t') * ϖ = (z - ϖ * t') - (z - ϖ * t) := by ring
  rw [this]
  exact (𝔓 ^ 2).sub_mem ht' ht

theorem tameCoeff_not_mem (hϖP : ϖ ∈ 𝔓) (hgen : ∀ x ∈ 𝔓, ∃ y : B, x - ϖ * y ∈ 𝔓 ^ 2)
    (hreg : ∀ c : B, c * ϖ ∈ 𝔓 ^ 2 → c ∈ 𝔓) {σ : G} (hσ : σ ∈ 𝔓.inertia G) : tameCoeff 𝔓 hϖP hgen hσ ∉ 𝔓 := by
  intro ht

  have h1 : σ • ϖ ∈ 𝔓 ^ 2 := by
    have h := tameCoeff_spec 𝔓 hϖP hgen hσ
    have h2 : ϖ * tameCoeff 𝔓 hϖP hgen hσ ∈ 𝔓 ^ 2 := by
      rw [pow_two]; exact Ideal.mul_mem_mul hϖP ht
    have : σ • ϖ = (σ • ϖ - ϖ * tameCoeff 𝔓 hϖP hgen hσ) + ϖ * tameCoeff 𝔓 hϖP hgen hσ := by ring
    rw [this]; exact (𝔓 ^ 2).add_mem h h2
  have h2 : ϖ ∈ 𝔓 ^ 2 := by
    have := smul_mem_sq_of_mem_inertia 𝔓 (Subgroup.inv_mem _ hσ) h1
    rwa [inv_smul_smul] at this
  have h3 : (1 : B) ∈ 𝔓 := hreg 1 (by rwa [one_mul])
  exact Ideal.IsPrime.one_notMem (by infer_instance) h3 |> absurd <| by trivial

noncomputable def tameCharFun (hϖP : ϖ ∈ 𝔓) (hgen : ∀ x ∈ 𝔓, ∃ y : B, x - ϖ * y ∈ 𝔓 ^ 2)
    (hreg : ∀ c : B, c * ϖ ∈ 𝔓 ^ 2 → c ∈ 𝔓) (σ : 𝔓.inertia G) : (B ⧸ 𝔓)ˣ :=
  letI : Field (B ⧸ 𝔓) := Ideal.Quotient.field 𝔓
  Units.mk0 (Ideal.Quotient.mk 𝔓 (tameCoeff 𝔓 hϖP hgen σ.2))
    (by rw [Ne, Ideal.Quotient.eq_zero_iff_mem]; exact tameCoeff_not_mem 𝔓 hϖP hgen hreg σ.2)

theorem val_tameCharFun (hϖP : ϖ ∈ 𝔓) (hgen : ∀ x ∈ 𝔓, ∃ y : B, x - ϖ * y ∈ 𝔓 ^ 2)
    (hreg : ∀ c : B, c * ϖ ∈ 𝔓 ^ 2 → c ∈ 𝔓) (σ : 𝔓.inertia G) :
    ((tameCharFun 𝔓 hϖP hgen hreg σ : (B ⧸ 𝔓)ˣ) : B ⧸ 𝔓) = Ideal.Quotient.mk 𝔓 (tameCoeff 𝔓 hϖP hgen σ.2) := rfl

noncomputable def tameChar (hϖP : ϖ ∈ 𝔓) (hgen : ∀ x ∈ 𝔓, ∃ y : B, x - ϖ * y ∈ 𝔓 ^ 2)
    (hreg : ∀ c : B, c * ϖ ∈ 𝔓 ^ 2 → c ∈ 𝔓) : (𝔓.inertia G) →* (B ⧸ 𝔓)ˣ where
  toFun := tameCharFun 𝔓 hϖP hgen hreg
  map_one' := by
    apply Units.ext
    rw [val_tameCharFun, Units.val_one, ← map_one (Ideal.Quotient.mk 𝔓), Ideal.Quotient.eq]
    refine tameCoeff_unique 𝔓 hreg (tameCoeff_spec 𝔓 hϖP hgen _) ?_
    simp
  map_mul' := by
    intro σ τ
    apply Units.ext
    rw [Units.val_mul, val_tameCharFun, val_tameCharFun, val_tameCharFun, ← map_mul, Ideal.Quotient.eq]
    refine tameCoeff_unique 𝔓 hreg (tameCoeff_spec 𝔓 hϖP hgen _) ?_

    set tσ := tameCoeff 𝔓 hϖP hgen σ.2
    set tτ := tameCoeff 𝔓 hϖP hgen τ.2
    have hτ := tameCoeff_spec 𝔓 hϖP hgen τ.2
    have hσ := tameCoeff_spec 𝔓 hϖP hgen σ.2
    have e1 : ((σ * τ : 𝔓.inertia G) : G) • ϖ = (σ : G) • ((τ : G) • ϖ) := mul_smul _ _ _

    have e2 : (σ : G) • ((τ : G) • ϖ) = (σ : G) • ((τ : G) • ϖ - ϖ * tτ) + ((σ : G) • ϖ) * ((σ : G) • tτ) := by
      rw [← smul_mul', ← smul_add]; congr 1; ring
    have hA : (σ : G) • ((τ : G) • ϖ - ϖ * tτ) ∈ 𝔓 ^ 2 := smul_mem_sq_of_mem_inertia 𝔓 σ.2 hτ

    have e3 : ((σ : G) • ϖ) * ((σ : G) • tτ) - ϖ * (tσ * tτ)
        = ((σ : G) • ϖ - ϖ * tσ) * ((σ : G) • tτ) + ϖ * (tσ * ((σ : G) • tτ - tτ)) := by ring
    have hB : ((σ : G) • ϖ) * ((σ : G) • tτ) - ϖ * (tσ * tτ) ∈ 𝔓 ^ 2 := by
      rw [e3]
      refine (𝔓 ^ 2).add_mem (Ideal.mul_mem_right _ _ hσ) ?_
      rw [pow_two]
      exact Ideal.mul_mem_mul hϖP (Ideal.mul_mem_left _ _ (σ.2 tτ))
    rw [e1, e2]
    have : (σ : G) • ((τ : G) • ϖ - ϖ * tτ) + ((σ : G) • ϖ) * ((σ : G) • tτ) - ϖ * (tσ * tτ)
        = (σ : G) • ((τ : G) • ϖ - ϖ * tτ) + (((σ : G) • ϖ) * ((σ : G) • tτ) - ϖ * (tσ * tτ)) := by ring
    rw [this]
    exact (𝔓 ^ 2).add_mem hA hB

variable (hϖP : ϖ ∈ 𝔓) (hgen : ∀ x ∈ 𝔓, ∃ y : B, x - ϖ * y ∈ 𝔓 ^ 2)
  (hreg : ∀ c : B, c * ϖ ∈ 𝔓 ^ 2 → c ∈ 𝔓)

theorem tameChar_apply (σ : 𝔓.inertia G) :
    ((tameChar (G := G) 𝔓 hϖP hgen hreg σ : (B ⧸ 𝔓)ˣ) : B ⧸ 𝔓) = Ideal.Quotient.mk 𝔓 (tameCoeff 𝔓 hϖP hgen σ.2) := rfl

theorem tameChar_eq_one_iff (σ : 𝔓.inertia G) :
    tameChar 𝔓 hϖP hgen hreg σ = 1 ↔ (σ : G) • ϖ - ϖ ∈ 𝔓 ^ 2 := by
  rw [← Units.val_eq_one, tameChar_apply, ← map_one (Ideal.Quotient.mk 𝔓), Ideal.Quotient.eq]
  constructor
  · intro h
    have hs := tameCoeff_spec 𝔓 hϖP hgen σ.2
    have : (σ : G) • ϖ - ϖ = ((σ : G) • ϖ - ϖ * tameCoeff 𝔓 hϖP hgen σ.2) + ϖ * (tameCoeff 𝔓 hϖP hgen σ.2 - 1) := by
      ring
    rw [this]
    refine (𝔓 ^ 2).add_mem hs ?_
    rw [pow_two]; exact Ideal.mul_mem_mul hϖP h
  · intro h
    exact tameCoeff_unique 𝔓 hreg (tameCoeff_spec 𝔓 hϖP hgen σ.2) (by rwa [mul_one])

theorem tameChar_eq_one_iff_forall [Finite (B ⧸ 𝔓)] (σ : 𝔓.inertia G) :
    tameChar 𝔓 hϖP hgen hreg σ = 1 ↔ ∀ x : B, (σ : G) • x - x ∈ 𝔓 ^ 2 := by
  rw [tameChar_eq_one_iff]
  exact ⟨fun h x => smul_sub_mem_sq_of_mem_inertia 𝔓 hϖP hgen σ.2 h x, fun h => h ϖ⟩

theorem isCyclic_range_tameChar [Finite (B ⧸ 𝔓)] : IsCyclic (tameChar (G := G) 𝔓 hϖP hgen hreg).range := by
  letI : Field (B ⧸ 𝔓) := Ideal.Quotient.field 𝔓
  exact isCyclic_of_subgroup_isDomain ((Units.coeHom (B ⧸ 𝔓)).comp (tameChar (G := G) 𝔓 hϖP hgen hreg).range.subtype)
    (Units.val_injective.comp Subtype.val_injective)

end TameChar
p2m_reactivate "P2MW.S_ValuationSubring_exists_ideal_ringOfIntegers_inertia_eq_map_restrictNormalHom.B6Inertia P2MW.S_ValuationSubring_exists_ideal_ringOfIntegers_inertia_eq_map_restrictNormalHom.ValuationSubring"

section Higher
variable {B : Type u} [CommRing B] {G : Type v} [Group G] [MulSemiringAction G B]
variable (𝔓 : Ideal B)

theorem smul_sub_pow_mul_mem_pow_succ {σ : G} (hσ : σ ∈ 𝔓.inertia G) {t : B}
    (h1 : ∀ x ∈ 𝔓, σ • x - t * x ∈ 𝔓 ^ 2) (k : ℕ) :
    ∀ x ∈ 𝔓 ^ k, σ • x - t ^ k * x ∈ 𝔓 ^ (k + 1) := by
  induction k with
  | zero =>
    intro x hx
    rw [pow_zero, one_mul, zero_add, pow_one]
    exact hσ x
  | succ k ih =>
    intro x hx
    rw [pow_succ] at hx
    refine Submodule.mul_induction_on hx (fun a ha b hb => ?_) (fun y z hy hz => ?_)
    ·
      have e : σ • (a * b) - t ^ (k + 1) * (a * b) = (σ • a - t ^ k * a) * (σ • b) + t ^ k * a * (σ • b - t * b) := by
        rw [smul_mul']; ring
      rw [e]
      refine (𝔓 ^ (k + 1 + 1)).add_mem ?_ ?_
      · rw [pow_succ]
        exact Ideal.mul_mem_mul (ih a ha) (smul_mem_of_mem_inertia 𝔓 hσ hb)
      · have : t ^ k * a * (σ • b - t * b) ∈ 𝔓 ^ k * 𝔓 ^ 2 :=
          Ideal.mul_mem_mul (Ideal.mul_mem_left _ _ ha) (h1 b hb)
        rw [← pow_add] at this
        exact this
    · have e : σ • (y + z) - t ^ (k + 1) * (y + z) = (σ • y - t ^ (k + 1) * y) + (σ • z - t ^ (k + 1) * z) := by
        rw [smul_add]; ring
      rw [e]; exact (𝔓 ^ (k + 1 + 1)).add_mem hy hz

theorem smul_sub_mem_pow_succ_of_forall {σ : G} (hσ : σ ∈ 𝔓.inertia G) (h1 : ∀ x : B, σ • x - x ∈ 𝔓 ^ 2)
    (k : ℕ) {x : B} (hx : x ∈ 𝔓 ^ k) : σ • x - x ∈ 𝔓 ^ (k + 1) := by
  have := smul_sub_pow_mul_mem_pow_succ 𝔓 hσ (t := 1) (fun x _ => by rw [one_mul]; exact h1 x) k x hx
  rwa [one_pow, one_mul] at this

theorem smul_sub_tameCoeff_mul_mem_sq [𝔓.IsMaximal] {ϖ : B} (hϖP : ϖ ∈ 𝔓)
    (hgen : ∀ x ∈ 𝔓, ∃ y : B, x - ϖ * y ∈ 𝔓 ^ 2) {σ : G} (hσ : σ ∈ 𝔓.inertia G)
    {x : B} (hx : x ∈ 𝔓) : σ • x - tameCoeff 𝔓 hϖP hgen hσ * x ∈ 𝔓 ^ 2 := by
  set t := tameCoeff 𝔓 hϖP hgen hσ with ht
  have hs : σ • ϖ - ϖ * t ∈ 𝔓 ^ 2 := tameCoeff_spec 𝔓 hϖP hgen hσ
  obtain ⟨y, hy⟩ := hgen x hx

  set p₂ := x - ϖ * y with hp
  have hx' : x = ϖ * y + p₂ := by rw [hp]; ring
  have e : σ • x - t * x = (σ • ϖ - ϖ * t) * (σ • y) + t * ϖ * (σ • y - y) + (σ • p₂ - t * p₂) := by
    conv_lhs => rw [hx']
    rw [smul_add, smul_mul']; ring
  rw [e]
  refine (𝔓 ^ 2).add_mem ((𝔓 ^ 2).add_mem (Ideal.mul_mem_right _ _ hs) ?_) ?_
  · rw [pow_two]; exact Ideal.mul_mem_mul (Ideal.mul_mem_left _ _ hϖP) (hσ y)
  · exact (𝔓 ^ 2).sub_mem (smul_mem_sq_of_mem_inertia 𝔓 hσ hy) (Ideal.mul_mem_left _ _ hy)

theorem tameChar_pow_eq_one_of_smul_eq [𝔓.IsMaximal] {ϖ : B} (hϖP : ϖ ∈ 𝔓)
    (hgen : ∀ x ∈ 𝔓, ∃ y : B, x - ϖ * y ∈ 𝔓 ^ 2) (hreg : ∀ c : B, c * ϖ ∈ 𝔓 ^ 2 → c ∈ 𝔓)
    (σ : 𝔓.inertia G) {k : ℕ} {α : B} (hαk : α ∈ 𝔓 ^ k) (hαreg : ∀ c : B, c * α ∈ 𝔓 ^ (k + 1) → c ∈ 𝔓)
    (hfix : (σ : G) • α = α) : tameChar 𝔓 hϖP hgen hreg σ ^ k = 1 := by
  letI : Field (B ⧸ 𝔓) := Ideal.Quotient.field 𝔓
  set t := tameCoeff 𝔓 hϖP hgen σ.2 with ht
  have h := smul_sub_pow_mul_mem_pow_succ 𝔓 σ.2 (t := t)
    (fun x hx => smul_sub_tameCoeff_mul_mem_sq 𝔓 hϖP hgen σ.2 hx) k α hαk
  rw [hfix] at h
  have e1 : (1 - t ^ k) * α = α - t ^ k * α := by ring
  have h2 : (1 - t ^ k) ∈ 𝔓 := hαreg _ (by rw [e1]; exact h)
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, tameChar_apply, Units.val_one, ← map_pow, ← map_one (Ideal.Quotient.mk 𝔓),
    eq_comm, Ideal.Quotient.eq]
  exact h2

end Higher
p2m_reactivate "P2MW.S_ValuationSubring_exists_ideal_ringOfIntegers_inertia_eq_map_restrictNormalHom.B6Inertia P2MW.S_ValuationSubring_exists_ideal_ringOfIntegers_inertia_eq_map_restrictNormalHom.ValuationSubring"

end GaloisRep.TameKernel
p2m_reactivate "P2MW.S_ValuationSubring_exists_ideal_ringOfIntegers_inertia_eq_map_restrictNormalHom.B6Inertia P2MW.S_ValuationSubring_exists_ideal_ringOfIntegers_inertia_eq_map_restrictNormalHom.ValuationSubring"
p2m_reactivate "P2MW.S_ValuationSubring_exists_ideal_ringOfIntegers_inertia_eq_map_restrictNormalHom.B6Inertia P2MW.S_ValuationSubring_exists_ideal_ringOfIntegers_inertia_eq_map_restrictNormalHom.ValuationSubring"

namespace GaloisRep
namespace TameNumerics

theorem apply_eq_one {H : Type*} [Group H] [Finite H] {M : Type*} [CommGroup M] (θ : H →* M)
    (hcyc : IsCyclic θ.range) {q n : ℕ} (hq : q.Prime) (hn : n.Coprime q)
    (hker : ∀ h : H, θ h = 1 → ∃ a : ℕ, orderOf h = q ^ a)
    {A : Type*} [CommGroup A] (ξ : H →* A) (hξn : ∀ h, ξ h ^ n = 1)
    (σ : H) {k : ℕ} (hk : θ σ ^ k = 1) (he : Nat.card H = n * k) :
    ξ σ = 1 := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩

  have hξker : ∀ h : H, θ h = 1 → ξ h = 1 := by
    intro h hh
    obtain ⟨a, ha⟩ := hker h hh
    have h1 : ξ h ^ q ^ a = 1 := by rw [← map_pow, ← ha, pow_orderOf_eq_one, map_one]
    have h2 : ξ h ^ n = 1 := hξn h
    have hcop : Nat.gcd (q ^ a) n = 1 := (Nat.Coprime.pow_left a hn.symm)
    have := (pow_gcd_eq_one (a := ξ h)).mpr ⟨h1, h2⟩
    rwa [hcop, pow_one] at this

  have hP : IsPGroup q θ.ker := by
    intro x
    obtain ⟨a, ha⟩ := hker x.1 x.2
    refine ⟨a, Subtype.ext ?_⟩
    rw [Subgroup.coe_pow, ← ha, pow_orderOf_eq_one, Subgroup.coe_one]
  obtain ⟨s, hs⟩ := IsPGroup.iff_card.mp hP

  have hcard : Nat.card H = Nat.card θ.ker * Nat.card θ.range := by
    rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange θ).toEquiv, mul_comm]
    exact Subgroup.card_eq_card_quotient_mul_card_subgroup θ.ker
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [mul_zero] at he
    exact (Nat.card_pos (α := H)).ne' he

  obtain ⟨g, hg⟩ := hcyc.exists_generator
  have hgc : orderOf g = Nat.card θ.range := orderOf_eq_card_of_forall_mem_zpowers hg

  obtain ⟨t, ht⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨θ σ, ⟨σ, rfl⟩⟩)

  have hct : (Nat.card θ.range : ℤ) ∣ t * k := by
    rw [← hgc, orderOf_dvd_iff_zpow_eq_one, zpow_mul, ht, zpow_natCast]
    exact Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one]; exact hk)

  have hnt : (n : ℤ) ∣ t := by
    have h0 : ((Nat.card H : ℕ) : ℤ) ∣ (q ^ s : ℕ) * (t * k) := by
      rw [hcard, hs, Nat.cast_mul]; exact mul_dvd_mul_left _ hct
    rw [he, Nat.cast_mul] at h0
    have e1 : ((n : ℤ) * k : ℤ) = k * n := mul_comm _ _
    have e2 : ((q ^ s : ℕ) : ℤ) * (t * k) = k * ((q ^ s : ℕ) * t) := by ring
    rw [e1, e2] at h0
    have hk0' : (k : ℤ) ≠ 0 := by exact_mod_cast hk0
    have h2 : (n : ℤ) ∣ (q ^ s : ℕ) * t := Int.dvd_of_mul_dvd_mul_left hk0' h0
    have hcop : IsCoprime (n : ℤ) ((q ^ s : ℕ) : ℤ) := by
      rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_natCast_natCast]
      exact Nat.Coprime.pow_right s hn
    exact hcop.dvd_of_dvd_mul_right (by rwa [mul_comm] at h2)
  obtain ⟨t', rfl⟩ := hnt

  obtain ⟨τ, hτ⟩ := (g ^ t').2
  have hθ : θ (σ * (τ ^ n)⁻¹) = 1 := by
    rw [map_mul, map_inv, map_pow, hτ, ← Subgroup.coe_pow, ← zpow_natCast, ← zpow_mul, mul_comm (t' : ℤ), ht,
      mul_inv_cancel]
  have h1 := hξker _ hθ
  rw [map_mul, map_inv, map_pow, hξn, inv_one, mul_one] at h1
  exact h1

end GaloisRep.TameNumerics
p2m_reactivate "P2MW.S_ValuationSubring_exists_ideal_ringOfIntegers_inertia_eq_map_restrictNormalHom.B6Inertia P2MW.S_ValuationSubring_exists_ideal_ringOfIntegers_inertia_eq_map_restrictNormalHom.ValuationSubring"
p2m_reactivate "P2MW.S_ValuationSubring_exists_ideal_ringOfIntegers_inertia_eq_map_restrictNormalHom.B6Inertia P2MW.S_ValuationSubring_exists_ideal_ringOfIntegers_inertia_eq_map_restrictNormalHom.ValuationSubring"

namespace GaloisRep
namespace Wild

variable {K L : Type} [Field K] [Field L] [Algebra K L] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀]
  (v : Valuation L Γ₀)

def IsWild (σ : L ≃ₐ[K] L) : Prop := ∀ z : L, z ≠ 0 → v (σ z - z) < v z

theorem IsWild.valuation_apply {σ : L ≃ₐ[K] L} (hw : IsWild v σ) (w : L) : v (σ w) = v w := by
  by_cases hw0 : w = 0
  · subst hw0; simp
  have h := Valuation.map_add_eq_of_lt_right v (hw w hw0)
  rwa [sub_add_cancel] at h

theorem IsWild.pow {σ : L ≃ₐ[K] L} (hw : IsWild v σ) (n : ℕ) : IsWild v (σ ^ n) := by
  induction n with
  | zero => intro z hz; simp [(map_ne_zero v).mpr hz, zero_lt_iff]
  | succ n ih =>
    intro z hz
    have hsplit : (σ ^ (n + 1)) z - z = σ ((σ ^ n) z - z) + (σ z - z) := by
      rw [pow_succ', AlgEquiv.mul_apply, map_sub]; ring
    rw [hsplit]
    refine Valuation.map_add_lt _ ?_ (hw z hz)
    rw [IsWild.valuation_apply v hw]
    exact ih z hz

theorem valuation_natCast_le_one (m : ℕ) : v (m : L) ≤ 1 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.cast_succ]
    exact (v.map_add _ _).trans (max_le ih (by rw [v.map_one]))

theorem valuation_intCast_le_one (m : ℤ) : v (m : L) ≤ 1 := by
  obtain ⟨k, rfl | rfl⟩ := m.eq_nat_or_neg
  · rw [Int.cast_natCast]; exact valuation_natCast_le_one v k
  · rw [Int.cast_neg, Int.cast_natCast, Valuation.map_neg]; exact valuation_natCast_le_one v k

theorem valuation_natCast_eq_one_of_coprime {q m : ℕ} (hq : v (q : L) < 1) (hm : Nat.Coprime m q) :
    v (m : L) = 1 := by
  have hle : v (m : L) ≤ 1 := valuation_natCast_le_one v m
  by_contra hne
  have hlt : v (m : L) < 1 := lt_of_le_of_ne hle hne
  have hg : (Int.gcd m q : ℤ) = 1 := by exact_mod_cast hm
  have hb := Int.gcd_eq_gcd_ab m q
  rw [hg] at hb
  have h1 : (1 : L) = (m : L) * (Int.gcdA m q : L) + (q : L) * (Int.gcdB m q : L) := by
    exact_mod_cast congrArg (Int.cast : ℤ → L) hb
  have : v (1 : L) < 1 := by
    rw [h1]
    refine Valuation.map_add_lt _ ?_ ?_
    · rw [map_mul]; exact mul_lt_one_of_lt_of_le hlt (valuation_intCast_le_one v _)
    · rw [map_mul]; exact mul_lt_one_of_lt_of_le hq (valuation_intCast_le_one v _)
  rw [map_one] at this
  exact lt_irrefl _ this

theorem IsWild.apply_eq_of_pow_apply_eq {σ : L ≃ₐ[K] L} (hw : IsWild v σ) {q m : ℕ} (hq : v (q : L) < 1)
    (hm : Nat.Coprime m q) (y : L) (hy : (σ ^ m) y = y) : σ y = y := by
  by_contra hne
  set w := σ y - y with hwdef
  have hw0 : w ≠ 0 := sub_ne_zero.mpr hne
  have htel : (Finset.range m).sum (fun i => (σ ^ i) w) = 0 := by
    have h := Finset.sum_range_sub (fun i => (σ ^ i) y) m
    simp only [pow_zero, AlgEquiv.one_apply] at h
    rw [hy, sub_self] at h
    rw [← h]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hwdef, map_sub, ← AlgEquiv.mul_apply, ← pow_succ]
  have hdec : (Finset.range m).sum (fun i => (σ ^ i) w)
      = (m : L) * w + (Finset.range m).sum (fun i => (σ ^ i) w - w) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    ring
  have hS : v ((Finset.range m).sum (fun i => (σ ^ i) w - w)) < v ((m : L) * w) := by
    rw [map_mul, valuation_natCast_eq_one_of_coprime v hq hm, one_mul]
    exact Valuation.map_sum_lt _ ((map_ne_zero _).mpr hw0) (fun i _ => (IsWild.pow v hw i) w hw0)
  have hval : v ((Finset.range m).sum (fun i => (σ ^ i) w)) = v ((m : L) * w) := by
    rw [hdec, add_comm]
    exact Valuation.map_add_eq_of_lt_right _ hS
  rw [htel, map_zero, map_mul, valuation_natCast_eq_one_of_coprime v hq hm, one_mul, eq_comm, map_eq_zero] at hval
  exact hw0 hval

theorem IsWild.orderOf_eq_pow {σ : L ≃ₐ[K] L} (hw : IsWild v σ) {q : ℕ} (hqp : q.Prime) (hq : v (q : L) < 1)
    (hfin : 0 < orderOf σ) : ∃ a : ℕ, orderOf σ = q ^ a := by
  obtain ⟨a, m, hqm, ho⟩ := Nat.exists_eq_pow_mul_and_not_dvd hfin.ne' q hqp.one_lt.ne'
  have hcop : Nat.Coprime m q := (Nat.coprime_comm).mp ((Nat.Prime.coprime_iff_not_dvd hqp).mpr hqm)
  have hw' : IsWild v (σ ^ (q ^ a)) := IsWild.pow v hw (q ^ a)
  have h1 : σ ^ (q ^ a) = 1 := by
    refine AlgEquiv.ext fun y => ?_
    refine IsWild.apply_eq_of_pow_apply_eq v hw' hq hcop y ?_
    rw [← pow_mul, ← ho, pow_orderOf_eq_one]
    rfl
  have h2 : orderOf σ ∣ q ^ a := orderOf_dvd_of_pow_eq_one h1
  obtain ⟨b, -, hb⟩ := (Nat.dvd_prime_pow hqp).mp h2
  exact ⟨b, hb⟩

end GaloisRep.Wild
p2m_reactivate "P2MW.S_ValuationSubring_exists_ideal_ringOfIntegers_inertia_eq_map_restrictNormalHom.B6Inertia P2MW.S_ValuationSubring_exists_ideal_ringOfIntegers_inertia_eq_map_restrictNormalHom.ValuationSubring"
p2m_reactivate "P2MW.S_ValuationSubring_exists_ideal_ringOfIntegers_inertia_eq_map_restrictNormalHom.B6Inertia P2MW.S_ValuationSubring_exists_ideal_ringOfIntegers_inertia_eq_map_restrictNormalHom.ValuationSubring"

namespace GaloisRep
namespace KUM

variable (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ L] [IsGalois ℚ L]
variable (A : ValuationSubring (AlgebraicClosure ℚ)) {q : ℕ} (hq : q.Prime) (hA : A.LiesOverPrime q)

local notation "𝔓" => ValuationSubring.primeBelow A L

theorem asIdeal_heightOneSpectrumBelow : (A.heightOneSpectrumBelow L hq hA).asIdeal = 𝔓 := rfl

theorem exp_neg_succ_lt (k : ℕ) : (WithZero.exp (-((k + 1 : ℕ) : ℤ)) : WithZero (Multiplicative ℤ)) < WithZero.exp (-(k : ℤ)) := by
  rw [WithZero.exp_lt_exp]; omega

include hq hA in

theorem mem_of_mul_mem_pow_succ {α : 𝓞 L} {k : ℕ}
    (hα : (A.heightOneSpectrumBelow L hq hA).intValuation α = WithZero.exp (-(k : ℤ)))
    (c : 𝓞 L) (hc : c * α ∈ 𝔓 ^ (k + 1)) : c ∈ 𝔓 := by
  set w := A.heightOneSpectrumBelow L hq hA
  rw [← asIdeal_heightOneSpectrumBelow L A hq hA, ← w.intValuation_le_pow_iff_mem, map_mul, hα] at hc
  rw [← asIdeal_heightOneSpectrumBelow L A hq hA, ← w.intValuation_lt_one_iff_mem]
  by_contra hge
  rw [not_lt] at hge
  have : WithZero.exp (-(k : ℤ)) ≤ w.intValuation c * WithZero.exp (-(k : ℤ)) :=
    le_mul_of_one_le_left zero_le' hge
  have h2 := this.trans hc
  rw [WithZero.exp_le_exp] at h2
  push_cast at h2
  omega

include hq hA in

theorem exists_uniformizer : ∃ ϖ : 𝓞 L, ϖ ∈ 𝔓 ∧ (∀ x ∈ 𝔓, ∃ y : 𝓞 L, x - ϖ * y ∈ 𝔓 ^ 2) ∧
    (∀ c : 𝓞 L, c * ϖ ∈ 𝔓 ^ 2 → c ∈ 𝔓) := by
  set w := A.heightOneSpectrumBelow L hq hA
  obtain ⟨ϖ, hϖ⟩ := w.intValuation_exists_uniformizer
  have hϖP : ϖ ∈ 𝔓 := by
    rw [← asIdeal_heightOneSpectrumBelow L A hq hA, ← w.intValuation_lt_one_iff_mem, hϖ, ← WithZero.exp_zero,
      WithZero.exp_lt_exp]; omega
  have hϖ2 : ϖ ∉ 𝔓 ^ 2 := by
    rw [← asIdeal_heightOneSpectrumBelow L A hq hA, ← w.intValuation_le_pow_iff_mem, hϖ, not_le, WithZero.exp_lt_exp]
    omega
  refine ⟨ϖ, hϖP, fun x hx => ?_, fun c hc => mem_of_mul_mem_pow_succ L A hq hA (k := 1) (by exact_mod_cast hϖ) c hc⟩

  have hI : Ideal.span {ϖ} ⊔ 𝔓 ^ 2 = 𝔓 ^ 1 := by
    haveI : (𝔓).IsPrime := (A.isMaximal_primeBelow L hq hA).isPrime
    refine Ideal.eq_prime_pow_of_succ_lt_of_le (A.primeBelow_ne_bot L hq hA) ?_ ?_
    · refine lt_of_le_of_ne le_sup_right fun h => hϖ2 ?_
      rw [h]; exact Ideal.mem_sup_left (Ideal.mem_span_singleton_self ϖ)
    · rw [pow_one]
      exact sup_le ((Ideal.span_singleton_le_iff_mem _).mpr hϖP) (Ideal.pow_le_self two_ne_zero)
  rw [pow_one] at hI
  have hx' : x ∈ Ideal.span {ϖ} ⊔ 𝔓 ^ 2 := by rw [hI]; exact hx
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hx'
  obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.mp ha
  refine ⟨y, ?_⟩
  have : x - ϖ * y = b := by rw [← hab]; ring
  rw [this]; exact hb

include hq hA in

theorem isWild_of_forall_smul_sub_mem_sq {τ : L ≃ₐ[ℚ] L} (hτ : τ ∈ (𝔓).inertia (L ≃ₐ[ℚ] L))
    (h1 : ∀ x : 𝓞 L, τ • x - x ∈ 𝔓 ^ 2) :
    Wild.IsWild (Valuation.comap (algebraMap L (AlgebraicClosure ℚ)) A.valuation) τ := by
  set w := A.heightOneSpectrumBelow L hq hA
  have hequiv := A.isEquiv_valuation_comap_adicValuation L hq hA

  have hint : ∀ x : 𝓞 L, x ≠ 0 →
      Valuation.comap (algebraMap L (AlgebraicClosure ℚ)) A.valuation ((τ (x : L)) - x)
        < Valuation.comap (algebraMap L (AlgebraicClosure ℚ)) A.valuation (x : L) := by
    intro x hx0

    have hne : w.intValuation x ≠ 0 := w.intValuation_ne_zero x hx0
    obtain ⟨z, hz⟩ : ∃ z : ℤ, w.intValuation x = WithZero.exp z :=
      ⟨WithZero.log (w.intValuation x), (WithZero.exp_log hne).symm⟩
    have hz0 : z ≤ 0 := by
      have := w.intValuation_le_one x
      rw [hz, ← WithZero.exp_zero, WithZero.exp_le_exp] at this
      exact this
    obtain ⟨k, hk⟩ : ∃ k : ℕ, z = -(k : ℤ) := ⟨z.natAbs, by omega⟩
    rw [hk] at hz
    have hxk : x ∈ 𝔓 ^ k := by
      rw [← asIdeal_heightOneSpectrumBelow L A hq hA, ← w.intValuation_le_pow_iff_mem, hz]
    have h2 : τ • x - x ∈ 𝔓 ^ (k + 1) := TameKernel.smul_sub_mem_pow_succ_of_forall (𝔓) hτ h1 k hxk
    rw [← asIdeal_heightOneSpectrumBelow L A hq hA, ← w.intValuation_le_pow_iff_mem] at h2
    have h3 : w.intValuation (τ • x - x) < w.intValuation x := by
      rw [hz]; exact lt_of_le_of_lt h2 (exp_neg_succ_lt k)

    have h4 : HeightOneSpectrum.valuation L w ((τ (x : L)) - x) < HeightOneSpectrum.valuation L w (x : L) := by
      have e1 : τ (x : L) - x = algebraMap (𝓞 L) L (τ • x - x) := by
        rw [map_sub, ← ValuationSubring.coe_smul_ringOfIntegers L τ x]
      have e2 : (x : L) = algebraMap (𝓞 L) L x := rfl
      rw [e1, e2, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap]
      exact h3
    exact (hequiv.lt_iff_lt).mpr h4

  set v := Valuation.comap (algebraMap L (AlgebraicClosure ℚ)) A.valuation with hv
  intro z hz
  obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 L) z
  have hy0 : (y : 𝓞 L) ≠ 0 := nonZeroDivisors.ne_zero hy
  have hx0 : (x : 𝓞 L) ≠ 0 := by
    rintro rfl; simp at hz
  have hx := hint x hx0
  have hy' := hint y hy0

  set x' : L := algebraMap (𝓞 L) L x with hx'
  set y' : L := algebraMap (𝓞 L) L y with hy''
  have hxL : (x : L) = x' := rfl
  have hyL : (y : L) = y' := rfl
  rw [hxL] at hx; rw [hyL] at hy'
  have hinj : Function.Injective (algebraMap (𝓞 L) L) := IsFractionRing.injective (𝓞 L) L
  have hy'0 : y' ≠ 0 := (map_ne_zero_iff _ hinj).mpr hy0
  have hx'0 : x' ≠ 0 := (map_ne_zero_iff _ hinj).mpr hx0
  have hvy : v (τ y') = v y' := by
    have h := Valuation.map_add_eq_of_lt_right v hy'
    rwa [sub_add_cancel] at h
  have hvx' : v x' ≠ 0 := (map_ne_zero v).mpr hx'0
  have hvy' : v y' ≠ 0 := (map_ne_zero v).mpr hy'0

  have hu : v (τ x' / x' - 1) < 1 := by
    rw [div_sub_one hx'0, map_div₀, div_lt_one₀ (zero_lt_iff.mpr hvx')]; exact hx
  have hu' : v (τ y' / y' - 1) < 1 := by
    rw [div_sub_one hy'0, map_div₀, div_lt_one₀ (zero_lt_iff.mpr hvy')]; exact hy'
  have hτy0 : τ y' ≠ 0 := by simpa using hy'0
  have hvu' : v (τ y' / y') = 1 := by rw [map_div₀, hvy, div_self hvy']

  have e : τ (x' / y') - x' / y' = (x' / y') * ((τ x' / x') / (τ y' / y') - 1) := by
    rw [map_div₀]; field_simp
  have hlast : v ((τ x' / x') / (τ y' / y') - 1) < 1 := by
    have e2 : (τ x' / x') / (τ y' / y') - 1 = ((τ x' / x' - 1) - (τ y' / y' - 1)) / (τ y' / y') := by
      field_simp
      try ring
    rw [e2, map_div₀, hvu', div_one]
    exact Valuation.map_sub_lt v hu hu'
  rw [e, map_mul]
  exact mul_lt_of_lt_one_right (zero_lt_iff.mpr ((map_ne_zero v).mpr (div_ne_zero hx'0 hy'0))) hlast

section Level
variable {Agrp : Type} [CommGroup Agrp]

local notation "Γℚ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

include hq hA in
theorem comap_valuation_natCast_lt_one :
    Valuation.comap (algebraMap L (AlgebraicClosure ℚ)) A.valuation (q : L) < 1 := by
  rw [Valuation.comap_apply, map_natCast]
  exact (ValuationSubring.mem_nonunits_iff A).mp hA

include hq hA in

theorem orderOf_eq_pow_of_forall_smul_sub_mem_sq {τ : L ≃ₐ[ℚ] L} (hτ : τ ∈ (𝔓).inertia (L ≃ₐ[ℚ] L))
    (h1 : ∀ x : 𝓞 L, τ • x - x ∈ 𝔓 ^ 2) : ∃ a : ℕ, orderOf τ = q ^ a :=
  Wild.IsWild.orderOf_eq_pow _ (isWild_of_forall_smul_sub_mem_sq L A hq hA hτ h1) hq
    (comap_valuation_natCast_lt_one L A hq hA) (orderOf_pos τ)

theorem xi_eq_of_restrict_eq (ξ : Γℚ → Agrp)
    (hmul : ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ τ ∈ A.inertiaSubgroupIn ℚ, ξ (σ * τ) = ξ σ * ξ τ)
    (hcont : ∀ σ ∈ A.inertiaSubgroupIn ℚ, (∀ x : L, σ (x : AlgebraicClosure ℚ) = x) → ξ σ = 1)
    {σ σ' : Γℚ} (hσ : σ ∈ A.inertiaSubgroupIn ℚ) (hσ' : σ' ∈ A.inertiaSubgroupIn ℚ)
    (h : AlgEquiv.restrictNormalHom L σ = AlgEquiv.restrictNormalHom L σ') : ξ σ = ξ σ' := by
  have hmem : σ⁻¹ * σ' ∈ A.inertiaSubgroupIn ℚ := Subgroup.mul_mem _ (Subgroup.inv_mem _ hσ) hσ'
  have hfix : ∀ x : L, (σ⁻¹ * σ') (x : AlgebraicClosure ℚ) = x := by
    intro x
    have h1 : AlgEquiv.restrictNormalHom L (σ⁻¹ * σ') = 1 := by rw [map_mul, map_inv, h, inv_mul_cancel]
    have h2 := ValuationSubring.algebraMap_restrictNormalHom_apply L (σ⁻¹ * σ') x
    rw [h1, AlgEquiv.one_apply] at h2
    exact h2.symm
  have h1 : ξ (σ⁻¹ * σ') = 1 := hcont _ hmem hfix
  have h2 : ξ σ' = ξ (σ * (σ⁻¹ * σ')) := by rw [mul_inv_cancel_left]
  rw [h2, hmul σ hσ _ hmem, h1, mul_one]

include hq hA in

theorem xi_eq_one_level {n : ℕ} (hn : n.Coprime q) (hn0 : 0 < n) (α : 𝓞 L)
    (hα : ((α : L) : AlgebraicClosure ℚ) ^ n = (q : AlgebraicClosure ℚ))
    (ξ : Γℚ → Agrp)
    (hmul : ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ τ ∈ A.inertiaSubgroupIn ℚ, ξ (σ * τ) = ξ σ * ξ τ)
    (hexp : ∀ σ ∈ A.inertiaSubgroupIn ℚ, ξ σ ^ n = 1)
    (hcont : ∀ σ ∈ A.inertiaSubgroupIn ℚ, (∀ x : L, σ (x : AlgebraicClosure ℚ) = x) → ξ σ = 1)
    {σ : Γℚ} (hσ : σ ∈ A.inertiaSubgroupIn ℚ) (hfix : σ ((α : L) : AlgebraicClosure ℚ) = (α : L)) :
    ξ σ = 1 := by
  classical
  haveI hmax : (𝔓).IsMaximal := A.isMaximal_primeBelow L hq hA
  haveI : Finite (𝓞 L ⧸ 𝔓) := Ideal.finiteQuotientOfFreeOfNeBot _ (A.primeBelow_ne_bot L hq hA)
  set G := (L ≃ₐ[ℚ] L)
  set res := AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := AlgebraicClosure ℚ) L with hres
  set H : Subgroup (L ≃ₐ[ℚ] L) := (𝔓).inertia (L ≃ₐ[ℚ] L) with hH
  have hD1 : (A.inertiaSubgroupIn ℚ).map res = H := A.map_restrictNormalHom_inertiaSubgroupIn_eq_inertia L hq hA

  obtain ⟨ϖ, hϖP, hgen, hreg⟩ := exists_uniformizer L A hq hA
  let θ : H →* (𝓞 L ⧸ 𝔓)ˣ := TameKernel.tameChar (𝔓) hϖP hgen hreg
  have hcyc : IsCyclic θ.range := TameKernel.isCyclic_range_tameChar (𝔓) hϖP hgen hreg
  have hker : ∀ h : H, θ h = 1 → ∃ a : ℕ, orderOf h = q ^ a := by
    intro h hh
    rw [TameKernel.tameChar_eq_one_iff_forall] at hh
    obtain ⟨a, ha⟩ := orderOf_eq_pow_of_forall_smul_sub_mem_sq L A hq hA h.2 hh
    exact ⟨a, by rw [← Subgroup.orderOf_coe, ha]⟩

  have hlift : ∀ h : H, ∃ τ : Γℚ, τ ∈ A.inertiaSubgroupIn ℚ ∧ res τ = h := by
    intro h
    have : (h : L ≃ₐ[ℚ] L) ∈ (A.inertiaSubgroupIn ℚ).map res := by rw [hD1]; exact h.2
    obtain ⟨τ, hτ, hτh⟩ := Subgroup.mem_map.mp this
    exact ⟨τ, hτ, hτh⟩
  choose lift hliftI hliftres using hlift

  let ξbar : H →* Agrp :=
    { toFun := fun h => ξ (lift h)
      map_one' := by
        refine hcont _ (hliftI 1) fun x => ?_
        have h2 := ValuationSubring.algebraMap_restrictNormalHom_apply L (lift 1) x
        rw [hliftres 1, OneMemClass.coe_one, AlgEquiv.one_apply] at h2
        exact h2.symm
      map_mul' := fun h h' => by
        have e : res (lift (h * h')) = res (lift h * lift h') := by
          rw [map_mul, hliftres, hliftres, hliftres, Subgroup.coe_mul]
        rw [xi_eq_of_restrict_eq L A ξ hmul hcont (hliftI _) (Subgroup.mul_mem _ (hliftI h) (hliftI h')) e]
        exact hmul _ (hliftI h) _ (hliftI h') }
  have hξbar : ∀ h : H, ξbar h = ξ (lift h) := fun h => rfl
  have hξn : ∀ h : H, ξbar h ^ n = 1 := fun h => hexp _ (hliftI h)

  have hσH : res σ ∈ H := by rw [← hD1]; exact Subgroup.mem_map_of_mem _ hσ
  set σbar : H := ⟨res σ, hσH⟩ with hσbar

  set w := A.heightOneSpectrumBelow L hq hA with hw
  have hα0 : α ≠ 0 := by
    rintro rfl
    simp only [map_zero, ZeroMemClass.coe_zero] at hα
    rw [zero_pow hn0.ne'] at hα
    exact (Nat.cast_ne_zero.mpr hq.ne_zero) hα.symm
  obtain ⟨k, hk⟩ : ∃ k : ℕ, w.intValuation α = WithZero.exp (-(k : ℤ)) := by
    have hne : w.intValuation α ≠ 0 := w.intValuation_ne_zero α hα0
    obtain ⟨z, hz⟩ : ∃ z : ℤ, w.intValuation α = WithZero.exp z :=
      ⟨WithZero.log (w.intValuation α), (WithZero.exp_log hne).symm⟩
    have hz0 : z ≤ 0 := by
      have := w.intValuation_le_one α
      rw [hz, ← WithZero.exp_zero, WithZero.exp_le_exp] at this
      exact this
    exact ⟨z.natAbs, by rw [hz]; congr 1; omega⟩
  have he : Nat.card H = n * k := by

    have h1 : Nat.card H = Ideal.ramificationIdx' (Ideal.span {(q : ℤ)}) (𝔓) := by
      rw [← A.card_map_restrictNormalHom_inertiaSubgroupIn L hq hA, hD1]

    have h2 : HeightOneSpectrum.valuation L w ((α : L)) ^ n
        = WithZero.exp (-(Ideal.ramificationIdx' (Ideal.span {(q : ℤ)}) (𝔓) : ℤ)) := by
      rw [← map_pow, ← A.adicValuation_natCast_eq_exp_neg_ramificationIdx L hq hA]
      congr 1
      apply (algebraMap L (AlgebraicClosure ℚ)).injective
      rw [map_pow, map_natCast]
      exact hα
    have h3 : HeightOneSpectrum.valuation L w ((α : L)) = WithZero.exp (-(k : ℤ)) := by
      rw [show ((α : L)) = algebraMap (𝓞 L) L α from rfl, HeightOneSpectrum.valuation_of_algebraMap, hk]
    rw [h3, ← WithZero.exp_nsmul, WithZero.exp_inj] at h2
    rw [h1]
    have : (n : ℤ) * k = (Ideal.ramificationIdx' (Ideal.span {(q : ℤ)}) (𝔓) : ℤ) := by
      rw [smul_neg, nsmul_eq_mul, neg_inj] at h2; exact h2
    exact_mod_cast this.symm

  have hαk : α ∈ (𝔓) ^ k := by
    rw [← asIdeal_heightOneSpectrumBelow L A hq hA, ← w.intValuation_le_pow_iff_mem, hk]
  have hfix' : (σbar : L ≃ₐ[ℚ] L) • α = α := by
    apply IsFractionRing.injective (𝓞 L) L
    change ((res σ • α : 𝓞 L) : L) = (α : L)
    rw [ValuationSubring.coe_smul_ringOfIntegers]
    apply (algebraMap L (AlgebraicClosure ℚ)).injective
    rw [ValuationSubring.algebraMap_restrictNormalHom_apply]
    exact hfix
  have hθk : θ σbar ^ k = 1 :=
    TameKernel.tameChar_pow_eq_one_of_smul_eq (𝔓) hϖP hgen hreg σbar hαk
      (mem_of_mul_mem_pow_succ L A hq hA hk) hfix'

  have hmain := TameNumerics.apply_eq_one θ hcyc hq hn hker ξbar hξn σbar hθk he
  rw [hξbar] at hmain
  rw [← hmain]
  exact xi_eq_of_restrict_eq L A ξ hmul hcont hσ (hliftI σbar) (by rw [hliftres])

end Level
p2m_reactivate "P2MW.S_ValuationSubring_exists_ideal_ringOfIntegers_inertia_eq_map_restrictNormalHom.B6Inertia P2MW.S_ValuationSubring_exists_ideal_ringOfIntegers_inertia_eq_map_restrictNormalHom.ValuationSubring"

end GaloisRep.KUM
p2m_reactivate "P2MW.S_ValuationSubring_exists_ideal_ringOfIntegers_inertia_eq_map_restrictNormalHom.B6Inertia P2MW.S_ValuationSubring_exists_ideal_ringOfIntegers_inertia_eq_map_restrictNormalHom.ValuationSubring"
p2m_reactivate "P2MW.S_ValuationSubring_exists_ideal_ringOfIntegers_inertia_eq_map_restrictNormalHom.B6Inertia P2MW.S_ValuationSubring_exists_ideal_ringOfIntegers_inertia_eq_map_restrictNormalHom.ValuationSubring"

namespace GaloisRep
namespace KUM

local notation "Γℚ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

theorem inertia_hom_eq_one_of_apply_kummerRoot_eq {q : ℕ} (hq : q.Prime)
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime q)
    {n : ℕ} (hn0 : 0 < n) (hn : n.Coprime q) (α : AlgebraicClosure ℚ) (hα : α ^ n = (q : AlgebraicClosure ℚ))
    {Agrp : Type} [CommGroup Agrp] (ξ : Γℚ → Agrp)
    (hmul : ∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ τ ∈ P.inertiaSubgroupIn ℚ, ξ (σ * τ) = ξ σ * ξ τ)
    (hexp : ∀ σ ∈ P.inertiaSubgroupIn ℚ, ξ σ ^ n = 1)
    (hcont : ∃ L : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ L ∧
      ∀ σ ∈ P.inertiaSubgroupIn ℚ, (∀ x ∈ L, σ x = x) → ξ σ = 1)
    {σ : Γℚ} (hσ : σ ∈ P.inertiaSubgroupIn ℚ) (hfix : σ α = α) :
    ξ σ = 1 := by
  classical
  obtain ⟨L₀, hL₀fin, hL₀⟩ := hcont
  haveI := hL₀fin

  have hαint : IsIntegral ℤ α := by
    refine IsIntegral.of_pow hn0 ?_
    rw [hα, ← map_natCast (algebraMap ℤ (AlgebraicClosure ℚ)) q]
    exact isIntegral_algebraMap
  have hαQ : IsIntegral ℚ α := by
    obtain ⟨p, hp, hp0⟩ := hαint
    refine ⟨p.map (Int.castRingHom ℚ), hp.map _, ?_⟩
    rw [Polynomial.eval₂_map]
    convert hp0 using 1
    exact congrArg (fun f => Polynomial.eval₂ f α p) (Subsingleton.elim _ _)

  haveI : FiniteDimensional ℚ (IntermediateField.adjoin ℚ ({α} : Set (AlgebraicClosure ℚ))) :=
    IntermediateField.adjoin.finiteDimensional hαQ
  let M : IntermediateField ℚ (AlgebraicClosure ℚ) := L₀ ⊔ IntermediateField.adjoin ℚ {α}
  haveI : FiniteDimensional ℚ M := inferInstance
  let L : IntermediateField ℚ (AlgebraicClosure ℚ) := IntermediateField.normalClosure ℚ M (AlgebraicClosure ℚ)
  haveI : FiniteDimensional ℚ L := normalClosure.is_finiteDimensional ℚ M (AlgebraicClosure ℚ)
  haveI : Normal ℚ L := normalClosure.normal ℚ M (AlgebraicClosure ℚ)
  haveI : Algebra.IsSeparable ℚ L := Algebra.IsAlgebraic.isSeparable_of_perfectField
  haveI : IsGalois ℚ L := ⟨⟩
  have hML : M ≤ L := IntermediateField.le_normalClosure M
  have hL₀L : L₀ ≤ L := le_sup_left.trans hML
  have hαL : α ∈ L := hML (le_sup_right (b := IntermediateField.adjoin ℚ {α})
    (IntermediateField.mem_adjoin_simple_self ℚ α))

  let αL : L := ⟨α, hαL⟩
  have hαLint : IsIntegral ℤ αL := by
    obtain ⟨p, hp, hp0⟩ := hαint
    refine ⟨p, hp, (algebraMap L (AlgebraicClosure ℚ)).injective ?_⟩
    rw [Polynomial.hom_eval₂, map_zero]
    exact hp0
  let α' : 𝓞 L := ⟨αL, (mem_integralClosure_iff ℤ L).mpr hαLint⟩
  have hα' : ((α' : L) : AlgebraicClosure ℚ) ^ n = (q : AlgebraicClosure ℚ) := hα
  have hcont' : ∀ τ ∈ P.inertiaSubgroupIn ℚ, (∀ x : L, τ (x : AlgebraicClosure ℚ) = x) → ξ τ = 1 :=
    fun τ hτ h => hL₀ τ hτ fun x hx => h ⟨x, hL₀L hx⟩
  exact xi_eq_one_level L P hq hP hn hn0 α' hα' ξ hmul hexp hcont' hσ hfix

end GaloisRep.KUM
p2m_reactivate "P2MW.S_ValuationSubring_exists_ideal_ringOfIntegers_inertia_eq_map_restrictNormalHom.B6Inertia P2MW.S_ValuationSubring_exists_ideal_ringOfIntegers_inertia_eq_map_restrictNormalHom.ValuationSubring"
p2m_reactivate "P2MW.S_ValuationSubring_exists_ideal_ringOfIntegers_inertia_eq_map_restrictNormalHom.B6Inertia P2MW.S_ValuationSubring_exists_ideal_ringOfIntegers_inertia_eq_map_restrictNormalHom.ValuationSubring"

namespace GaloisRep
namespace KUM
theorem level_dictionary (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ F] [IsGalois ℚ F]
    (P : ValuationSubring (AlgebraicClosure ℚ)) {q : ℕ} (hq : q.Prime) (hP : P.LiesOverPrime q) :
    ∃ Q : Ideal (𝓞 F), Q.IsMaximal ∧ Finite (𝓞 F ⧸ Q) ∧ (q : 𝓞 F) ∈ Q ∧
      (∀ x : 𝓞 F, P.valuation (algebraMap F (AlgebraicClosure ℚ) x) ≤ 1) ∧
      (∀ x : 𝓞 F, x ∈ Q ↔ P.valuation (algebraMap F (AlgebraicClosure ℚ) x) < 1) ∧
      (P.inertiaSubgroupIn ℚ).map (AlgEquiv.restrictNormalHom F) = Q.inertia (F ≃ₐ[ℚ] F) ∧
      (∀ τ : F ≃ₐ[ℚ] F, τ ∈ Q.inertia (F ≃ₐ[ℚ] F) → (∀ x : 𝓞 F, τ • x - x ∈ Q ^ 2) → ∃ a : ℕ, orderOf τ = q ^ a) ∧
      (∃ ϖ : 𝓞 F, ϖ ∈ Q ∧ (∀ x ∈ Q, ∃ y : 𝓞 F, x - ϖ * y ∈ Q ^ 2) ∧ (∀ c : 𝓞 F, c * ϖ ∈ Q ^ 2 → c ∈ Q)) := by
  refine ⟨P.primeBelow F, P.isMaximal_primeBelow F hq hP,
    Ideal.finiteQuotientOfFreeOfNeBot _ (P.primeBelow_ne_bot F hq hP), P.natCast_mem_primeBelow F hP,
    fun x => P.valuation_algebraMap_ringOfIntegers_le_one F x, fun x => P.mem_primeBelow_iff F,
    P.map_restrictNormalHom_inertiaSubgroupIn_eq_inertia F hq hP,
    fun τ hτ h1 => orderOf_eq_pow_of_forall_smul_sub_mem_sq F P hq hP hτ h1, exists_uniformizer F P hq hP⟩
end GaloisRep.KUM
p2m_reactivate "P2MW.S_ValuationSubring_exists_ideal_ringOfIntegers_inertia_eq_map_restrictNormalHom.B6Inertia P2MW.S_ValuationSubring_exists_ideal_ringOfIntegers_inertia_eq_map_restrictNormalHom.ValuationSubring"
p2m_reactivate "P2MW.S_ValuationSubring_exists_ideal_ringOfIntegers_inertia_eq_map_restrictNormalHom.B6Inertia P2MW.S_ValuationSubring_exists_ideal_ringOfIntegers_inertia_eq_map_restrictNormalHom.ValuationSubring"

theorem solution
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
  GaloisRep.KUM.level_dictionary F P hq hP

end S_ValuationSubring_exists_ideal_ringOfIntegers_inertia_eq_map_restrictNormalHom
end P2MW
export P2MW.S_ValuationSubring_exists_ideal_ringOfIntegers_inertia_eq_map_restrictNormalHom (solution)
