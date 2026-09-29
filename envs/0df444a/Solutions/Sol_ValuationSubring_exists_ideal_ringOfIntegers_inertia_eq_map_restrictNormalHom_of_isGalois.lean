-- Prove2me | solution 1 for ValuationSubring.exists_ideal_ringOfIntegers_inertia_eq_map_restrictNormalHom_of_isGalois
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/fe9f4ad2-cea0-54af-81fb-e16745dfa668

import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_exists_ideal_ringOfIntegers_inertia_eq_map_restrictNormalHom_of_isGalois

set_option autoImplicit false

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
p2m_reactivate "P2MW.S_ValuationSubring_exists_ideal_ringOfIntegers_inertia_eq_map_restrictNormalHom_of_isGalois.B6Inertia"

namespace ValuationSubring
p2m_export "ValuationSubring" "comap coe_mem_nonunits_iff mem_comap smul_mem_pointwise_smul_iff inertiaSubgroup toSubring ext nonunits mem_nonunits_iff valuation_le_one mk smul_mem_pointwise_smul valuation_lt_one_iff mem_pointwise_smul_iff_inv_smul_mem decompositionSubgroup valuation_le_one_iff algebra valuation inclusion LiesOverPrime inertiaSubgroupIn"
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
theorem mem_primeBelow_iff {x : 𝓞 L} :
    x ∈ A.primeBelow L ↔ A.valuation (algebraMap L (AlgebraicClosure ℚ) (x : L)) < 1 := by
  rw [primeBelow, Ideal.mem_comap, valuation_lt_one_iff]
  rfl

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
theorem primeBelow_liesOver (hp : p.Prime) (hA : A.LiesOverPrime p) :
    (A.primeBelow L).LiesOver (Ideal.span {(p : ℤ)}) :=
  ⟨(A.under_int_primeBelow L hp hA).symm⟩

theorem isMaximal_primeBelow [FiniteDimensional ℚ L] (hp : p.Prime) (hA : A.LiesOverPrime p) :
    (A.primeBelow L).IsMaximal :=
  (A.primeBelow_isPrime L).isMaximal (A.primeBelow_ne_bot L hp hA)

end Integers
p2m_reactivate "P2MW.S_ValuationSubring_exists_ideal_ringOfIntegers_inertia_eq_map_restrictNormalHom_of_isGalois.B6Inertia"

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
p2m_reactivate "P2MW.S_ValuationSubring_exists_ideal_ringOfIntegers_inertia_eq_map_restrictNormalHom_of_isGalois.B6Inertia"

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

theorem dvd_ramificationIdx_of_valuation_pow_eq (hp : p.Prime) (hA : A.LiesOverPrime p)
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

end Ramification
p2m_reactivate "P2MW.S_ValuationSubring_exists_ideal_ringOfIntegers_inertia_eq_map_restrictNormalHom_of_isGalois.B6Inertia"

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
p2m_reactivate "P2MW.S_ValuationSubring_exists_ideal_ringOfIntegers_inertia_eq_map_restrictNormalHom_of_isGalois.B6Inertia"

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

theorem natCast_mem_center (hA : A.LiesOverPrime p) :
    (p : integralClosure ℤ (AlgebraicClosure ℚ)) ∈ A.center := by
  rw [mem_center_iff, ← mem_nonunits_iff]
  simp at hA ⊢
  exact hA

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
p2m_reactivate "P2MW.S_ValuationSubring_exists_ideal_ringOfIntegers_inertia_eq_map_restrictNormalHom_of_isGalois.B6Inertia"

end ValuationSubring
p2m_reactivate "P2MW.S_ValuationSubring_exists_ideal_ringOfIntegers_inertia_eq_map_restrictNormalHom_of_isGalois.B6Inertia P2MW.S_ValuationSubring_exists_ideal_ringOfIntegers_inertia_eq_map_restrictNormalHom_of_isGalois.ValuationSubring"

namespace ResidueSurj

open scoped Pointwise in

theorem mem_inertiaSubgroupIn_iff_forall {K L : Type*} [Field K] [Field L] [Algebra K L]
    (A : ValuationSubring L) (σ : L ≃ₐ[K] L) :
    σ ∈ A.inertiaSubgroupIn K ↔
      (∀ x : L, σ.symm x ∈ A ↔ x ∈ A) ∧ ∀ a : L, a ∈ A → σ a - a ∈ A.nonunits := by
  constructor
  · rintro ⟨d, hd, rfl⟩
    have hstab : (d : L ≃ₐ[K] L) • A = A := d.2
    refine ⟨fun x => ?_, fun a ha => ?_⟩
    · conv_rhs => rw [← hstab]
      rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
      rfl
    · have hker : MulSemiringAction.toRingAut (A.decompositionSubgroup K) (IsLocalRing.ResidueField A) d = 1 := hd
      have h1 : d • IsLocalRing.residue A ⟨a, ha⟩ = IsLocalRing.residue A ⟨a, ha⟩ := by
        have := RingEquiv.congr_fun hker (IsLocalRing.residue A ⟨a, ha⟩)
        simpa using this
      rw [← IsLocalRing.ResidueField.residue_smul] at h1
      rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff] at h1
      have h2 := ValuationSubring.coe_mem_nonunits_iff.mpr h1
      simp at h2
      exact h2
  · rintro ⟨hA, hres⟩
    have hstab : σ • A = A := by
      ext x
      rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
      exact hA x
    refine ⟨⟨σ, hstab⟩, ?_, rfl⟩
    change MulSemiringAction.toRingAut (A.decompositionSubgroup K) (IsLocalRing.ResidueField A) ⟨σ, hstab⟩ = 1
    apply RingEquiv.ext
    intro r
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective r
    change (⟨σ, hstab⟩ : A.decompositionSubgroup K) • IsLocalRing.residue A a = IsLocalRing.residue A a
    rw [← IsLocalRing.ResidueField.residue_smul, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
    apply ValuationSubring.coe_mem_nonunits_iff.mp
    have h__af := hres a a.2
    simp at h__af ⊢
    exact h__af

theorem mem_inertiaSubgroupIn_iff_of_forall_apply_eq
    {K E L : Type*} [Field K] [Field E] [Field L] [Algebra K L] [Algebra E L]
    (A : ValuationSubring L) (σ : L ≃ₐ[K] L) (τ : L ≃ₐ[E] L) (h : ∀ x : L, σ x = τ x) :
    σ ∈ A.inertiaSubgroupIn K ↔ τ ∈ A.inertiaSubgroupIn E := by
  have hsymm : ∀ x : L, σ.symm x = τ.symm x := fun x => by
    apply τ.injective
    rw [← h, AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply]
  rw [mem_inertiaSubgroupIn_iff_forall, mem_inertiaSubgroupIn_iff_forall]
  simp only [hsymm, h]

end ResidueSurj
p2m_reactivate "P2MW.S_ValuationSubring_exists_ideal_ringOfIntegers_inertia_eq_map_restrictNormalHom_of_isGalois.B6Inertia P2MW.S_ValuationSubring_exists_ideal_ringOfIntegers_inertia_eq_map_restrictNormalHom_of_isGalois.ValuationSubring"

namespace INSF_node13

section IntegersF

variable (A : ValuationSubring (AlgebraicClosure ℚ))
  (M : Type) [Field M] [NumberField M] [Algebra M (AlgebraicClosure ℚ)]

private theorem _root_.INSF_node13.algebraMap_ringOfIntegers_mem (x : 𝓞 M) :
    algebraMap M (AlgebraicClosure ℚ) (x : M) ∈ A :=
  A.mem_of_isIntegral_int
    (map_isIntegral_int (algebraMap M (AlgebraicClosure ℚ))
      (NumberField.RingOfIntegers.isIntegral_coe x))

p2m_export "INSF_node13" "algebraMap_ringOfIntegers_mem"
private theorem _root_.INSF_node13.valuation_algebraMap_ringOfIntegers_le_one (x : 𝓞 M) :
    A.valuation (algebraMap M (AlgebraicClosure ℚ) (x : M)) ≤ 1 :=
  (A.valuation_le_one_iff _).mpr (algebraMap_ringOfIntegers_mem A M x)

p2m_export "INSF_node13" "valuation_algebraMap_ringOfIntegers_le_one"

private def _root_.INSF_node13.ringOfIntegersToValuationSubring : 𝓞 M →+* A :=
  ((algebraMap M (AlgebraicClosure ℚ)).comp (algebraMap (𝓞 M) M)).codRestrict A.toSubring
    (fun x => algebraMap_ringOfIntegers_mem A M x)

p2m_export "INSF_node13" "ringOfIntegersToValuationSubring"

def primeUnder : Ideal (𝓞 M) :=
  (IsLocalRing.maximalIdeal A).comap (ringOfIntegersToValuationSubring A M)

theorem mem_primeUnder_iff {x : 𝓞 M} :
    x ∈ primeUnder A M ↔ A.valuation (algebraMap M (AlgebraicClosure ℚ) (x : M)) < 1 := by
  rw [primeUnder, Ideal.mem_comap, ValuationSubring.valuation_lt_one_iff]
  rfl

theorem mem_primeUnder_iff_mem_nonunits {x : 𝓞 M} :
    x ∈ primeUnder A M ↔ algebraMap M (AlgebraicClosure ℚ) (x : M) ∈ A.nonunits := by
  rw [mem_primeUnder_iff, ValuationSubring.mem_nonunits_iff]

scoped instance primeUnder_isPrime : (primeUnder A M).IsPrime :=
  Ideal.IsPrime.comap _

variable {p : ℕ}

theorem natCast_mem_primeUnder (hA : A.LiesOverPrime p) : (p : 𝓞 M) ∈ primeUnder A M := by
  rw [mem_primeUnder_iff_mem_nonunits]
  change algebraMap M (AlgebraicClosure ℚ) (algebraMap (𝓞 M) M (p : 𝓞 M)) ∈ A.nonunits
  rw [map_natCast, map_natCast]
  exact hA

theorem primeUnder_ne_bot (hp : p.Prime) (hA : A.LiesOverPrime p) : primeUnder A M ≠ ⊥ := by
  intro h
  have := natCast_mem_primeUnder A M hA
  rw [h, Ideal.mem_bot, Nat.cast_eq_zero] at this
  exact hp.ne_zero this

theorem isMaximal_primeUnder (hp : p.Prime) (hA : A.LiesOverPrime p) :
    (primeUnder A M).IsMaximal :=
  (primeUnder_isPrime A M).isMaximal (primeUnder_ne_bot A M hp hA)

end IntegersF
p2m_reactivate "P2MW.S_ValuationSubring_exists_ideal_ringOfIntegers_inertia_eq_map_restrictNormalHom_of_isGalois.B6Inertia P2MW.S_ValuationSubring_exists_ideal_ringOfIntegers_inertia_eq_map_restrictNormalHom_of_isGalois.ValuationSubring"

section LiftF

variable (A : ValuationSubring (AlgebraicClosure ℚ))
  (F : Type) [Field F] [NumberField F] [Algebra F (AlgebraicClosure ℚ)]
  (L : IntermediateField F (AlgebraicClosure ℚ)) [FiniteDimensional F L]
  {p : ℕ}

scoped instance instNumberField_intermediateField : NumberField L := NumberField.of_module_finite F L

theorem algebraMap_restrictNormalHom_apply [Normal F L]
    (σ : AlgebraicClosure ℚ ≃ₐ[F] AlgebraicClosure ℚ) (x : L) :
    algebraMap L (AlgebraicClosure ℚ) (AlgEquiv.restrictNormalHom L σ x) =
      σ (algebraMap L (AlgebraicClosure ℚ) x) :=
  AlgEquiv.restrictNormal_commutes σ L x

variable [IsGalois F L]

theorem exists_lift_valuation_sub_lt_one_of_mem_inertia (τ : L ≃ₐ[F] L)
    (hτ : τ ∈ (primeUnder A L).inertia (L ≃ₐ[F] L)) :
    ∃ σ : AlgebraicClosure ℚ ≃ₐ[F] AlgebraicClosure ℚ, AlgEquiv.restrictNormalHom L σ = τ ∧
      ∀ b : integralClosure ℤ (AlgebraicClosure ℚ),
        A.valuation (σ b - b) < 1 := by
  classical
  haveI : Algebra.IsAlgebraic F (AlgebraicClosure ℚ) := Algebra.IsAlgebraic.tower_top (K := ℚ) F
  haveI : Normal F (AlgebraicClosure ℚ) := Normal.tower_top_of_normal ℚ F _
  haveI : Algebra.IsSeparable F (AlgebraicClosure ℚ) :=
    Algebra.isSeparable_tower_top_of_isSeparable ℚ F _
  haveI : Algebra.IsAlgebraic L (AlgebraicClosure ℚ) := Algebra.IsAlgebraic.tower_top (K := F) L
  haveI : Algebra.IsIntegral L (AlgebraicClosure ℚ) :=
    Algebra.isAlgebraic_iff_isIntegral.mp inferInstance
  haveI : Normal L (AlgebraicClosure ℚ) := Normal.tower_top_of_normal F L _
  haveI : Algebra.IsSeparable L (AlgebraicClosure ℚ) :=
    Algebra.isSeparable_tower_top_of_isSeparable F L _
  haveI : IsGalois L (AlgebraicClosure ℚ) := ⟨⟩
  set Q : Ideal (𝓞 L) := primeUnder A L with hQdef
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
    rw [h𝔔def, ValuationSubring.mem_center_iff, hf_coe, hQdef, mem_primeUnder_iff]
  haveI h𝔔lies : 𝔔.LiesOver Q := ⟨by
    ext x
    rw [Ideal.under_def, Ideal.mem_comap, hmemQ]⟩

  let rshF : (AlgebraicClosure ℚ ≃ₐ[F] AlgebraicClosure ℚ) →*
      (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :=
    { toFun := fun g => g.restrictScalars ℚ
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hrshF_apply : ∀ (g : AlgebraicClosure ℚ ≃ₐ[F] AlgebraicClosure ℚ) (x : AlgebraicClosure ℚ),
      rshF g x = g x := fun _ _ => rfl
  let rshLF : (AlgebraicClosure ℚ ≃ₐ[L] AlgebraicClosure ℚ) →*
      (AlgebraicClosure ℚ ≃ₐ[F] AlgebraicClosure ℚ) :=
    { toFun := fun g => g.restrictScalars F
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  let rsh : (AlgebraicClosure ℚ ≃ₐ[L] AlgebraicClosure ℚ) →*
      (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) := rshF.comp rshLF
  have hrsh_apply : ∀ (g : AlgebraicClosure ℚ ≃ₐ[L] AlgebraicClosure ℚ) (x : AlgebraicClosure ℚ),
      rsh g x = g x := fun _ _ => rfl
  have hrsh_comp : ∀ g : AlgebraicClosure ℚ ≃ₐ[L] AlgebraicClosure ℚ, rshF (rshLF g) = rsh g :=
    fun _ => rfl

  have hres : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[F] AlgebraicClosure ℚ) (x : 𝓞 L),
      rshF σ • algebraMap (𝓞 L) (integralClosure ℤ (AlgebraicClosure ℚ)) x =
        algebraMap (𝓞 L) (integralClosure ℤ (AlgebraicClosure ℚ))
          ((AlgEquiv.restrictNormalHom L σ) • x) := by
    intro σ x
    apply Subtype.ext
    change σ (algebraMap L (AlgebraicClosure ℚ) (x : L)) =
      algebraMap L (AlgebraicClosure ℚ) ((σ.restrictNormal L) (x : L))
    exact (AlgEquiv.restrictNormal_commutes σ L (x : L)).symm

  have hresL : ∀ g : AlgebraicClosure ℚ ≃ₐ[L] AlgebraicClosure ℚ,
      AlgEquiv.restrictNormalHom L (rshLF g) = 1 := by
    intro g
    refine AlgEquiv.ext fun x => (algebraMap L (AlgebraicClosure ℚ)).injective ?_
    change algebraMap L (AlgebraicClosure ℚ) (((rshLF g).restrictNormal L) x) =
      algebraMap L (AlgebraicClosure ℚ) x
    rw [AlgEquiv.restrictNormal_commutes]
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
      convert hq0 using 2
      rfl
      rfl
    refine ⟨⟨y, hyint⟩, Subtype.ext ?_⟩
    rw [hf_coe]
    exact hy⟩

  obtain ⟨σ₀, hσ₀⟩ := AlgEquiv.restrictNormalHom_surjective (F := F) (K₁ := L) (E := AlgebraicClosure ℚ) τ
  have hunder : Ideal.under (𝓞 L) (rshF σ₀ • 𝔔 : Ideal (integralClosure ℤ (AlgebraicClosure ℚ))) =
      Ideal.under (𝓞 L) 𝔔 := by
    ext x
    rw [Ideal.mem_under, Ideal.mem_under, Ideal.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv, hres,
      hmemQ, hmemQ, map_inv, hσ₀]
    conv_rhs => rw [← hstabτ]
    rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem]
  obtain ⟨g, hg⟩ := Algebra.IsInvariant.exists_smul_of_under_eq_of_profinite
      (A := 𝓞 L) (G := AlgebraicClosure ℚ ≃ₐ[L] AlgebraicClosure ℚ)
      (rshF σ₀ • 𝔔 : Ideal (integralClosure ℤ (AlgebraicClosure ℚ))) 𝔔 hunder

  set σ₁ : AlgebraicClosure ℚ ≃ₐ[F] AlgebraicClosure ℚ := rshLF g * σ₀ with hσ₁def
  have hσ₁G : rshF σ₁ = rsh g * rshF σ₀ := by
    rw [hσ₁def, map_mul, hrsh_comp]
  have hσ₁𝔔 : rshF σ₁ • 𝔔 = 𝔔 := by rw [hσ₁G, mul_smul, ← hrsI, ← hg]
  have hσ₁L : AlgEquiv.restrictNormalHom L σ₁ = τ := by
    rw [hσ₁def, map_mul, hresL, one_mul, hσ₀]

  have hσ₁stab : rshF σ₁ ∈
      MulAction.stabilizer (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) 𝔔 := hσ₁𝔔
  let φ₀ : (integralClosure ℤ (AlgebraicClosure ℚ) ⧸ 𝔔) ≃ₐ[ℤ ⧸ 𝔔.under ℤ]
      (integralClosure ℤ (AlgebraicClosure ℚ) ⧸ 𝔔) :=
    Ideal.Quotient.stabilizerHom 𝔔 (𝔔.under ℤ) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      ⟨rshF σ₁, hσ₁stab⟩
  have hστQ : ∀ x : 𝓞 L, Ideal.Quotient.mk 𝔔 (rshF σ₁ •
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
      φ (Ideal.Quotient.mk 𝔔 b) = Ideal.Quotient.mk 𝔔 (rshF σ₁ • b) :=
    fun b => rfl
  obtain ⟨t, ht⟩ :=
    Ideal.Quotient.stabilizerHom_surjective_of_profinite
      (G := AlgebraicClosure ℚ ≃ₐ[L] AlgebraicClosure ℚ) Q 𝔔 φ
  have ht' : ∀ b : integralClosure ℤ (AlgebraicClosure ℚ),
      Ideal.Quotient.mk 𝔔 ((t : AlgebraicClosure ℚ ≃ₐ[L] AlgebraicClosure ℚ) • b) =
        Ideal.Quotient.mk 𝔔 (rshF σ₁ • b) := by
    intro b
    have h := congrArg (fun e => e (Ideal.Quotient.mk 𝔔 b)) ht
    simp only [Ideal.Quotient.stabilizerHom_apply, hφ] at h
    exact h

  have hσG : rshF ((rshLF (t : AlgebraicClosure ℚ ≃ₐ[L] AlgebraicClosure ℚ))⁻¹ * σ₁) =
      (rsh (t : AlgebraicClosure ℚ ≃ₐ[L] AlgebraicClosure ℚ))⁻¹ * rshF σ₁ := by
    rw [map_mul, map_inv, hrsh_comp]
  refine ⟨(rshLF (t : AlgebraicClosure ℚ ≃ₐ[L] AlgebraicClosure ℚ))⁻¹ * σ₁, ?_, ?_⟩
  · rw [map_mul, map_inv, hresL, inv_one, one_mul, hσ₁L]
  · intro b
    have h1 : rshF σ₁ • b - (t : AlgebraicClosure ℚ ≃ₐ[L] AlgebraicClosure ℚ) • b ∈ 𝔔 := by
      rw [← Ideal.Quotient.eq]
      exact (ht' b).symm
    have h2 : ((t⁻¹ : MulAction.stabilizer (AlgebraicClosure ℚ ≃ₐ[L] AlgebraicClosure ℚ) 𝔔) :
        AlgebraicClosure ℚ ≃ₐ[L] AlgebraicClosure ℚ) •
          (rshF σ₁ • b - (t : AlgebraicClosure ℚ ≃ₐ[L] AlgebraicClosure ℚ) • b) ∈ 𝔔 := by
      have hmem := (Ideal.smul_mem_pointwise_smul_iff
        (a := ((t⁻¹ : MulAction.stabilizer (AlgebraicClosure ℚ ≃ₐ[L] AlgebraicClosure ℚ) 𝔔) :
          AlgebraicClosure ℚ ≃ₐ[L] AlgebraicClosure ℚ))).mpr h1
      rwa [MulAction.mem_stabilizer_iff.mp (t⁻¹).2] at hmem
    have h3 : ((t⁻¹ : MulAction.stabilizer (AlgebraicClosure ℚ ≃ₐ[L] AlgebraicClosure ℚ) 𝔔) :
        AlgebraicClosure ℚ ≃ₐ[L] AlgebraicClosure ℚ) •
          (rshF σ₁ • b - (t : AlgebraicClosure ℚ ≃ₐ[L] AlgebraicClosure ℚ) • b) =
        ((rsh (t : AlgebraicClosure ℚ ≃ₐ[L] AlgebraicClosure ℚ))⁻¹ * rshF σ₁) • b - b := by
      rw [Subgroup.coe_inv, smul_sub, inv_smul_smul, hrs, map_inv]
      simp only [mul_smul]
    rw [h3, ← hσG] at h2
    exact A.mem_center_iff.mp h2

theorem exists_mem_inertiaSubgroupIn_restrictNormalHom_eq (hp : p.Prime) (hA : A.LiesOverPrime p)
    (τ : L ≃ₐ[F] L) (hτ : τ ∈ (primeUnder A L).inertia (L ≃ₐ[F] L)) :
    ∃ σ ∈ A.inertiaSubgroupIn F, AlgEquiv.restrictNormalHom L σ = τ := by
  obtain ⟨σ, hσL, hσ⟩ := exists_lift_valuation_sub_lt_one_of_mem_inertia A F L τ hτ
  have h1 : σ.restrictScalars ℚ ∈ A.inertiaSubgroupIn ℚ :=
    A.mem_inertiaSubgroupIn_of_forall_valuation_sub_lt_one hp hA (σ.restrictScalars ℚ) hσ
  exact ⟨σ, (ResidueSurj.mem_inertiaSubgroupIn_iff_of_forall_apply_eq A (σ.restrictScalars ℚ) σ
    (fun _ => rfl)).mp h1, hσL⟩

theorem map_restrictNormalHom_inertiaSubgroupIn_le :
    (A.inertiaSubgroupIn F).map (AlgEquiv.restrictNormalHom L) ≤
      (primeUnder A L).inertia (L ≃ₐ[F] L) := by
  rintro _ ⟨σ, hσ, rfl⟩
  refine AddSubgroup.mem_inertia.mpr fun x => ?_
  change AlgEquiv.restrictNormalHom L σ • x - x ∈ primeUnder A L
  rw [mem_primeUnder_iff]
  have hcoe : (((AlgEquiv.restrictNormalHom L σ • x - x : 𝓞 L)) : L) =
      AlgEquiv.restrictNormalHom L σ (x : L) - x := rfl
  rw [hcoe, map_sub, algebraMap_restrictNormalHom_apply]
  exact (ValuationSubring.valuation_sub_lt_one_of_mem_inertiaSubgroupIn' A hσ
    (algebraMap_ringOfIntegers_mem A L x)).2

theorem map_restrictNormalHom_inertiaSubgroupIn_eq_inertia (hp : p.Prime) (hA : A.LiesOverPrime p) :
    (A.inertiaSubgroupIn F).map (AlgEquiv.restrictNormalHom L) =
      (primeUnder A L).inertia (L ≃ₐ[F] L) := by
  refine le_antisymm (map_restrictNormalHom_inertiaSubgroupIn_le A F L) fun τ hτ => ?_
  obtain ⟨σ, hσ, rfl⟩ := exists_mem_inertiaSubgroupIn_restrictNormalHom_eq A F L hp hA τ hτ
  exact Subgroup.mem_map_of_mem _ hσ

end LiftF
p2m_reactivate "P2MW.S_ValuationSubring_exists_ideal_ringOfIntegers_inertia_eq_map_restrictNormalHom_of_isGalois.B6Inertia P2MW.S_ValuationSubring_exists_ideal_ringOfIntegers_inertia_eq_map_restrictNormalHom_of_isGalois.ValuationSubring"

theorem main
    (F : Type) [Field F] [NumberField F] [Algebra F (AlgebraicClosure ℚ)]
    (P : ValuationSubring (AlgebraicClosure ℚ)) (q : ℕ) [Fact q.Prime] (hP : P.LiesOverPrime q)
    (M : IntermediateField F (AlgebraicClosure ℚ)) [FiniteDimensional F ↥M] [IsGalois F ↥M] :
    ∃ Q : Ideal (NumberField.RingOfIntegers ↥M), Q.IsMaximal ∧
      (∀ x : NumberField.RingOfIntegers ↥M, P.valuation (algebraMap ↥M (AlgebraicClosure ℚ) x) ≤ 1) ∧
      (∀ x : NumberField.RingOfIntegers ↥M, x ∈ Q ↔ P.valuation (algebraMap ↥M (AlgebraicClosure ℚ) x) < 1) ∧
      (P.inertiaSubgroupIn F).map (AlgEquiv.restrictNormalHom ↥M) = Q.inertia (↥M ≃ₐ[F] ↥M) :=
  ⟨primeUnder P M, isMaximal_primeUnder P M (Fact.out : q.Prime) hP,
    fun x => valuation_algebraMap_ringOfIntegers_le_one P M x, fun _ => mem_primeUnder_iff P M,
    map_restrictNormalHom_inertiaSubgroupIn_eq_inertia P F M (Fact.out : q.Prime) hP⟩

end INSF_node13
p2m_reactivate "P2MW.S_ValuationSubring_exists_ideal_ringOfIntegers_inertia_eq_map_restrictNormalHom_of_isGalois.B6Inertia P2MW.S_ValuationSubring_exists_ideal_ringOfIntegers_inertia_eq_map_restrictNormalHom_of_isGalois.ValuationSubring P2MW.S_ValuationSubring_exists_ideal_ringOfIntegers_inertia_eq_map_restrictNormalHom_of_isGalois.INSF_node13"

theorem solution
    (F : Type) [Field F] [NumberField F] [Algebra F (AlgebraicClosure ℚ)]
    (P : ValuationSubring (AlgebraicClosure ℚ)) (q : ℕ) [Fact q.Prime] (hP : P.LiesOverPrime q)
    (M : IntermediateField F (AlgebraicClosure ℚ)) [FiniteDimensional F ↥M] [IsGalois F ↥M] :
    ∃ Q : Ideal (NumberField.RingOfIntegers ↥M), Q.IsMaximal ∧
      (∀ x : NumberField.RingOfIntegers ↥M, P.valuation (algebraMap ↥M (AlgebraicClosure ℚ) x) ≤ 1) ∧
      (∀ x : NumberField.RingOfIntegers ↥M, x ∈ Q ↔ P.valuation (algebraMap ↥M (AlgebraicClosure ℚ) x) < 1) ∧
      (P.inertiaSubgroupIn F).map (AlgEquiv.restrictNormalHom ↥M) = Q.inertia (↥M ≃ₐ[F] ↥M) :=
  INSF_node13.main F P q hP M

end
end S_ValuationSubring_exists_ideal_ringOfIntegers_inertia_eq_map_restrictNormalHom_of_isGalois
end P2MW
export P2MW.S_ValuationSubring_exists_ideal_ringOfIntegers_inertia_eq_map_restrictNormalHom_of_isGalois (solution)
