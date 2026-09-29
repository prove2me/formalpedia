-- Prove2me | solution 1 for WeierstrassCurve.card_range_galoisRep_three_le_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/c918f1e2-6df5-59b0-8751-4794f72e6302

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
import Definitions.Def_FLTPrelim_Ramification
import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.LinearAlgebra.Projection
import Mathlib.NumberTheory.NumberField.Discriminant.Different
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.RingTheory.KrullDimension.Basic
import Definitions.Def_GaloisRep_Residual
import Theorems.Thm_WeierstrassCurve_apply_eq_self_of_galoisRep_eq_one_of_pow_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_card_range_galoisRep_three_le_two
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.Affine.mem_fibSet WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.placeOf_asIdeal"

p2m_open_scoped "NumberField P2MW.S_WeierstrassCurve_card_range_galoisRep_three_le_two.NumberField Pointwise"

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
p2m_reactivate "P2MW.S_WeierstrassCurve_card_range_galoisRep_three_le_two.B6Inertia"

namespace ValuationSubring
p2m_export "ValuationSubring" "comap mem_comap smul_mem_pointwise_smul_iff inertiaSubgroup toSubring algebraMap_apply ext zero_mem nonunits mem_nonunits_iff valuation_le_one mk smul_mem_pointwise_smul mem_top algebraMap_injective valuation_lt_one_iff mem_pointwise_smul_iff_inv_smul_mem decompositionSubgroup valuation_le_one_iff algebra valuation LiesOverPrime inertiaSubgroupIn"
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
private theorem _root_.ValuationSubring.primeBelow_liesOver (hp : p.Prime) (hA : A.LiesOverPrime p) :
    (A.primeBelow L).LiesOver (Ideal.span {(p : ℤ)}) :=
  ⟨(A.under_int_primeBelow L hp hA).symm⟩

p2m_export "ValuationSubring" "primeBelow_liesOver"
private theorem _root_.ValuationSubring.isMaximal_primeBelow [FiniteDimensional ℚ L] (hp : p.Prime) (hA : A.LiesOverPrime p) :
    (A.primeBelow L).IsMaximal :=
  (A.primeBelow_isPrime L).isMaximal (A.primeBelow_ne_bot L hp hA)

p2m_export "ValuationSubring" "isMaximal_primeBelow"
end Integers
p2m_reactivate "P2MW.S_WeierstrassCurve_card_range_galoisRep_three_le_two.B6Inertia"

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
p2m_reactivate "P2MW.S_WeierstrassCurve_card_range_galoisRep_three_le_two.B6Inertia"

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
p2m_reactivate "P2MW.S_WeierstrassCurve_card_range_galoisRep_three_le_two.B6Inertia"

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
p2m_reactivate "P2MW.S_WeierstrassCurve_card_range_galoisRep_three_le_two.B6Inertia"

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
  first | exact hA | simpa using hA | simpa +zetaDelta using hA

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
p2m_reactivate "P2MW.S_WeierstrassCurve_card_range_galoisRep_three_le_two.B6Inertia"

section Lift

variable (A : ValuationSubring (AlgebraicClosure ℚ)) (L : IntermediateField ℚ (AlgebraicClosure ℚ))
  {p : ℕ}

theorem algebraMap_restrictNormalHom_apply [Normal ℚ L]
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : L) :
    algebraMap L (AlgebraicClosure ℚ) (AlgEquiv.restrictNormalHom L σ x) =
      σ (algebraMap L (AlgebraicClosure ℚ) x) :=
  AlgEquiv.restrictNormal_commutes σ L x

variable [IsGalois ℚ L]

set_option maxHeartbeats 8000000 in

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
    first | exact h | simpa only [Ideal.Quotient.stabilizerHom_apply, hφ] using h | simpa +zetaDelta only [Ideal.Quotient.stabilizerHom_apply, hφ] using h

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
p2m_reactivate "P2MW.S_WeierstrassCurve_card_range_galoisRep_three_le_two.B6Inertia"

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
      (L ≃ₐ[ℚ] L),
    Ideal.ramificationIdx'_eq_ramificationIdx (Ideal.span {(p : ℤ)}) (A.primeBelow L)
      (by simpa [Ideal.span_singleton_eq_bot] using hp.ne_zero)]

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
  rw [Ideal.ramificationIdx'_eq_ramificationIdx (Ideal.span {(p : ℤ)}) (A.primeBelow L)
      (by simpa [Ideal.span_singleton_eq_bot] using hp.ne_zero),
    Algebra.isUnramifiedAt_iff_of_isDedekindDomain]

p2m_export "ValuationSubring" "ramificationIdx_primeBelow_eq_one_iff_isUnramifiedAt"

private theorem _root_.ValuationSubring.map_restrictNormalHom_inertiaSubgroupIn_eq_bot_iff_isUnramifiedAt (hp : p.Prime)
    (hA : A.LiesOverPrime p) :
    (A.inertiaSubgroupIn ℚ).map (AlgEquiv.restrictNormalHom L) = ⊥ ↔
      Algebra.IsUnramifiedAt ℤ (A.primeBelow L) := by
  rw [A.map_restrictNormalHom_inertiaSubgroupIn_eq_bot_iff L hp hA,
    A.ramificationIdx_primeBelow_eq_one_iff_isUnramifiedAt L hp hA]

p2m_export "ValuationSubring" "map_restrictNormalHom_inertiaSubgroupIn_eq_bot_iff_isUnramifiedAt"
end Dictionary
p2m_reactivate "P2MW.S_WeierstrassCurve_card_range_galoisRep_three_le_two.B6Inertia"

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
p2m_reactivate "P2MW.S_WeierstrassCurve_card_range_galoisRep_three_le_two.B6Inertia"

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
  rw [A.card_map_restrictNormalHom_inertiaSubgroupIn L hp hA,
    Ideal.ramificationIdx'_eq_ramificationIdx (Ideal.span {(p : ℤ)}) (A.primeBelow L)
      (by simpa [Ideal.span_singleton_eq_bot] using hp.ne_zero),
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
p2m_reactivate "P2MW.S_WeierstrassCurve_card_range_galoisRep_three_le_two.B6Inertia"

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
p2m_reactivate "P2MW.S_WeierstrassCurve_card_range_galoisRep_three_le_two.B6Inertia"

end ValuationSubring
p2m_reactivate "P2MW.S_WeierstrassCurve_card_range_galoisRep_three_le_two.B6Inertia P2MW.S_WeierstrassCurve_card_range_galoisRep_three_le_two.ValuationSubring"

end
p2m_reactivate "P2MW.S_WeierstrassCurve_card_range_galoisRep_three_le_two.B6Inertia P2MW.S_WeierstrassCurve_card_range_galoisRep_three_le_two.ValuationSubring"

open Module

namespace LinearMap
p2m_export "LinearMap" "coe_comp comp_zero range rank fst_comp_inr snd mul_apply' snd_comp_inl trace_prodMap' inl_apply map_span fst_apply codRestrict inr fst trace_comp_comm' mk coe_coe pi ext comp isIntegral trace finiteDimensional prodMap comp_assoc restrictScalars rangeRestrict ker inl mem_ker comp_apply trace_conj' restrict coe_restrict_apply coe_injective conjugate"
p2m_open "LinearMap"

section TraceAdditivity

variable {F : Type*} [Field F]

theorem trace_prod_eq_trace_fst_add_trace_snd {M N : Type*} [AddCommGroup M] [Module F M]
    [AddCommGroup N] [Module F N] [FiniteDimensional F M] [FiniteDimensional F N]
    (g : (M × N) →ₗ[F] (M × N)) :
    trace F (M × N) g = trace F M (fst F M N ∘ₗ g ∘ₗ inl F M N) +
      trace F N (snd F M N ∘ₗ g ∘ₗ inr F M N) := by
  have hg : g = (fst F M N ∘ₗ g ∘ₗ inl F M N).prodMap (snd F M N ∘ₗ g ∘ₗ inr F M N)
      + inl F M N ∘ₗ ((fst F M N ∘ₗ g ∘ₗ inr F M N) ∘ₗ snd F M N)
      + inr F M N ∘ₗ ((snd F M N ∘ₗ g ∘ₗ inl F M N) ∘ₗ fst F M N) := by
    ext <;> simp [Prod.mk_zero_zero]
  have h1 : trace F (M × N)
      (inl F M N ∘ₗ ((fst F M N ∘ₗ g ∘ₗ inr F M N) ∘ₗ snd F M N)) = 0 := by
    rw [trace_comp_comm', comp_assoc, snd_comp_inl, comp_zero, map_zero]
  have h2 : trace F (M × N)
      (inr F M N ∘ₗ ((snd F M N ∘ₗ g ∘ₗ inl F M N) ∘ₗ fst F M N)) = 0 := by
    rw [trace_comp_comm', comp_assoc, fst_comp_inr, comp_zero, map_zero]
  conv_lhs => rw [hg]
  rw [map_add, map_add, h1, h2, add_zero, add_zero, trace_prodMap']

theorem trace_eq_trace_restrict_add_trace_quotient {V : Type*} [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (W : Submodule F V) (T : V →ₗ[F] V) (hT : W ≤ W.comap T) :
    trace F V T = trace F W (T.restrict fun _ hx => hT hx) +
      trace F (V ⧸ W) (W.mapQ W T hT) := by
  obtain ⟨W', hW⟩ := W.exists_isCompl
  set e := Submodule.prodEquivOfIsCompl W W' hW with he
  rw [← trace_conj' T e.symm, trace_prod_eq_trace_fst_add_trace_snd]
  congr 1
  · congr 1
    ext w
    have hTw : T (w : V) = ((⟨T w, hT w.2⟩ : W) : V) := rfl
    simp only [coe_comp, Function.comp_apply, inl_apply, fst_apply, LinearEquiv.coe_coe,
      LinearEquiv.conj_apply, LinearEquiv.symm_symm, he, Submodule.coe_prodEquivOfIsCompl',
      ZeroMemClass.coe_zero, add_zero, coe_restrict_apply]
    rw [hTw, Submodule.prodEquivOfIsCompl_symm_apply_left]
  · rw [← trace_conj' (W.mapQ W T hT) (Submodule.quotientEquivOfIsCompl W W' hW)]
    congr 1
    ext w
    simp [he, LinearEquiv.conj_apply]

end TraceAdditivity
p2m_reactivate "P2MW.S_WeierstrassCurve_card_range_galoisRep_three_le_two.B6Inertia P2MW.S_WeierstrassCurve_card_range_galoisRep_three_le_two.ValuationSubring"

end LinearMap
p2m_reactivate "P2MW.S_WeierstrassCurve_card_range_galoisRep_three_le_two.B6Inertia P2MW.S_WeierstrassCurve_card_range_galoisRep_three_le_two.ValuationSubring"

namespace Ideal
p2m_export "Ideal" "map_le_iff_le_comap height prime_iff_isPrime Quotient.eq_zero_iff_mem mem_span_singleton IsPrime.comap under_def Quotient.stabilizerHom_surjective_of_profinite Quotient.eq inertia comap_bot_of_injective IsPrime.ne_top map_span IsPrime.under absNorm_span_singleton image_subset_nonunits_valuationSubring pi quotientToQuotientRangePowQuotSucc_injective quotientToQuotientRangePowQuotSucc Quotient.stabilizerHom mem_bot span Quotient.algebraMap_mk_of_liesOver powQuotSuccInclusion_injective span_singleton_eq_bot mem_under mul_le_left liesOver_span_iff span_singleton_prime quotientToQuotientRangePowQuotSucc_mk powQuotSuccInclusion count_associates_factors_eq one_eq_top map_quotient_self Quotient.stabilizerHom_apply IsMaximal Quotient.mk dvd_iff_le Quotient.field mul_mem_left smul_mem_pointwise_smul quotEquivOfEq map span_singleton_le_iff_mem ramificationIdxIn_eq_ramificationIdx IsDedekindDomain.ramificationIdx_ne_zero_of_liesOver le_pow_ramificationIdx ext le_of_dvd quotientToQuotientRangePowQuotSucc_surjective LiesOver inertia_le_stabilizer IsPrime mem_map_of_mem ramificationIdx' ResidueField comap_map_of_surjective mem_comap mem_pointwise_smul_iff_inv_smul_mem eq_prime_pow_mul_coprime IsDedekindDomain.ramificationIdx'_eq_normalizedFactors_count finiteQuotientOfFreeOfNeBot under comap_top quotientMulEquivQuotientProd comap isPrime_of_prime map_eq_bot_iff_of_injective smul_mem_pointwise_smul_iff pow_right_strictAnti Quotient.algebraQuotientOfRamificationIdxNeZero card_inertia_eq_ramificationIdxIn ramificationIdx_bot' Quotient.mk_surjective isCoprime_iff_sup_eq Quotient.algebraQuotientOfLEComap absNorm_dvd_absNorm_of_le map_top"
p2m_open "Ideal"

section GradedTrace

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] (p : Ideal R) (P : Ideal S)

attribute [local instance] Ideal.Quotient.field

noncomputable def mulRestrictPowQuot (z : S ⧸ P ^ ramificationIdx' p P)
    (I : Ideal (S ⧸ P ^ ramificationIdx' p P)) : I →ₗ[R ⧸ p] I where
  toFun x := ⟨z * x, I.mul_mem_left z x.2⟩
  map_add' x y := Subtype.ext <| by simp [mul_add]
  map_smul' c x := Subtype.ext <| by simp

@[scoped simp]
theorem mulRestrictPowQuot_apply_coe (z : S ⧸ P ^ ramificationIdx' p P)
    (I : Ideal (S ⧸ P ^ ramificationIdx' p P)) (x : I) :
    (mulRestrictPowQuot p P z I x : S ⧸ P ^ ramificationIdx' p P) = z * x := rfl

attribute [local instance] Ideal.Quotient.algebraQuotientOfRamificationIdxNeZero

variable [p.IsMaximal] [P.IsPrime] [IsDedekindDomain S] [hne : NeZero (ramificationIdx' p P)]

theorem trace_mulRestrictPowQuot_map_pow [Module.Finite (R ⧸ p) (S ⧸ P ^ ramificationIdx' p P)]
    (hP0 : P ≠ ⊥) (z : S) {i k : ℕ} (hik : i + k = ramificationIdx' p P) :
    LinearMap.trace (R ⧸ p) _
      (mulRestrictPowQuot p P (Ideal.Quotient.mk (P ^ ramificationIdx' p P) z)
        ((P ^ i).map (Ideal.Quotient.mk (P ^ ramificationIdx' p P)))) =
      k • Algebra.trace (R ⧸ p) (S ⧸ P) (Ideal.Quotient.mk P z) := by
  induction k generalizing i with
  | zero =>
    rw [zero_nsmul]
    rw [add_zero] at hik
    subst hik
    have hT0 : mulRestrictPowQuot p P (Ideal.Quotient.mk (P ^ ramificationIdx' p P) z)
        ((P ^ ramificationIdx' p P).map (Ideal.Quotient.mk (P ^ ramificationIdx' p P))) = 0 := by
      apply LinearMap.ext
      intro x
      have hx : (x : S ⧸ P ^ ramificationIdx' p P) ∈
          (⊥ : Ideal (S ⧸ P ^ ramificationIdx' p P)) := by
        rw [← Ideal.map_quotient_self (P ^ ramificationIdx' p P)]
        exact x.2
      rw [Ideal.mem_bot] at hx
      exact Subtype.ext (by simp [hx])
    rw [hT0, map_zero]
  | succ k ih =>
    have hi : i < ramificationIdx' p P := by omega

    set W := LinearMap.range (powQuotSuccInclusion p P i) with hW
    set T := mulRestrictPowQuot p P (Ideal.Quotient.mk (P ^ ramificationIdx' p P) z)
      ((P ^ i).map (Ideal.Quotient.mk (P ^ ramificationIdx' p P))) with hT
    have hWT : W ≤ W.comap T := by
      rintro _ ⟨y, rfl⟩
      refine ⟨mulRestrictPowQuot p P (Ideal.Quotient.mk (P ^ ramificationIdx' p P) z) _ y, ?_⟩
      ext; rfl
    rw [LinearMap.trace_eq_trace_restrict_add_trace_quotient W T hWT, succ_nsmul]
    congr 1
    ·
      rw [← ih (i := i + 1) (by omega)]
      let φ := LinearEquiv.ofInjective _ (powQuotSuccInclusion_injective p P i)
      rw [← LinearMap.trace_conj' _ φ]
      congr 1
      ext w
      obtain ⟨y, rfl⟩ := φ.surjective w
      simp only [LinearMap.coe_restrict_apply, LinearEquiv.conj_apply, LinearMap.coe_comp,
        LinearEquiv.coe_coe, Function.comp_apply, LinearEquiv.symm_apply_apply]
      simp [φ, T, LinearEquiv.ofInjective_apply]
    ·
      obtain ⟨a, a_mem, a_notMem⟩ := SetLike.exists_of_lt
        (Ideal.pow_right_strictAnti P hP0 (Ideal.IsPrime.ne_top inferInstance)
          (le_refl i.succ))
      let ψ := LinearEquiv.ofBijective (quotientToQuotientRangePowQuotSucc p P a_mem)
        ⟨quotientToQuotientRangePowQuotSucc_injective p P hi a_mem a_notMem,
          quotientToQuotientRangePowQuotSucc_surjective p P hP0 hi a_mem a_notMem⟩
      rw [Algebra.trace_apply, ← LinearMap.trace_conj' _ ψ]
      congr 1
      apply LinearMap.ext
      intro q
      obtain ⟨x, rfl⟩ := ψ.surjective q
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
      simp only [LinearEquiv.conj_apply, LinearMap.coe_comp, LinearEquiv.coe_coe,
        Function.comp_apply, LinearEquiv.symm_apply_apply]
      have hmk : ∀ y : S, Ideal.Quotient.mk P y = Submodule.Quotient.mk y := fun _ => rfl
      rw [Algebra.coe_lmul_eq_mul, LinearMap.mul_apply', ← map_mul, hmk, hmk]
      simp only [ψ, LinearEquiv.ofBijective_apply, quotientToQuotientRangePowQuotSucc_mk,
        Submodule.mapQ_apply]
      congr 1
      apply Subtype.ext
      simp only [T, mulRestrictPowQuot_apply_coe, ← map_mul]
      congr 1
      ring

theorem trace_quotient_pow_ramificationIdx [Module.Finite (R ⧸ p) (S ⧸ P ^ ramificationIdx' p P)]
    (hP0 : P ≠ ⊥) (z : S) :
    Algebra.trace (R ⧸ p) (S ⧸ P ^ ramificationIdx' p P)
        (Ideal.Quotient.mk (P ^ ramificationIdx' p P) z) =
      ramificationIdx' p P • Algebra.trace (R ⧸ p) (S ⧸ P) (Ideal.Quotient.mk P z) := by
  rw [← trace_mulRestrictPowQuot_map_pow p P hP0 z (i := 0) (zero_add _), Algebra.trace_apply]

  have htop : ∀ y : S ⧸ P ^ ramificationIdx' p P,
      y ∈ (P ^ 0).map (Ideal.Quotient.mk (P ^ ramificationIdx' p P)) := by
    intro y
    simp [Ideal.one_eq_top, Ideal.map_top]
  let ι : ((P ^ 0).map (Ideal.Quotient.mk (P ^ ramificationIdx' p P))) →ₗ[R ⧸ p]
      (S ⧸ P ^ ramificationIdx' p P) :=
    { toFun := fun x => (x : S ⧸ P ^ ramificationIdx' p P)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hι : Function.Bijective ι :=
    ⟨fun a b h => Subtype.ext h, fun y => ⟨⟨y, htop y⟩, rfl⟩⟩
  let τ := LinearEquiv.ofBijective ι hι
  rw [← LinearMap.trace_conj' _ τ]
  congr 1
  apply LinearMap.ext
  intro y
  obtain ⟨x, rfl⟩ := τ.surjective y
  simp only [LinearEquiv.conj_apply, LinearMap.coe_comp, LinearEquiv.coe_coe,
    Function.comp_apply, LinearEquiv.symm_apply_apply]
  rfl

end GradedTrace
p2m_reactivate "P2MW.S_WeierstrassCurve_card_range_galoisRep_three_le_two.B6Inertia P2MW.S_WeierstrassCurve_card_range_galoisRep_three_le_two.ValuationSubring"

end Ideal
p2m_reactivate "P2MW.S_WeierstrassCurve_card_range_galoisRep_three_le_two.B6Inertia P2MW.S_WeierstrassCurve_card_range_galoisRep_three_le_two.ValuationSubring P2MW.S_WeierstrassCurve_card_range_galoisRep_three_le_two.Ideal"

section TameDifferent

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

variable (A : Type*) {B : Type*} [CommRing A] [CommRing B] [Algebra A B]
  [IsDedekindDomain A] [IsDedekindDomain B] [Module.IsTorsionFree A B] [Module.Finite A B]
  [Algebra.IsSeparable (FractionRing A) (FractionRing B)]

attribute [local instance] Ideal.Quotient.field

p2m_open "Ideal P2MW.S_WeierstrassCurve_card_range_galoisRep_three_le_two.Ideal NumberField.Ideal UniqueFactorizationMonoid"

theorem not_pow_ramificationIdx_dvd_differentIdeal {p : Ideal A} [p.IsMaximal] (hp : p ≠ ⊥)
    (P : Ideal B) [P.IsMaximal] [P.LiesOver p] [Algebra.IsSeparable (A ⧸ p) (B ⧸ P)]
    (he : ((ramificationIdx' p P : ℕ) : A ⧸ p) ≠ 0) :
    ¬ P ^ ramificationIdx' p P ∣ differentIdeal A B := by
  classical
  have he0 : ramificationIdx' p P ≠ 0 := by
    rintro h
    simp [h] at he
  haveI : NeZero (ramificationIdx' p P) := ⟨he0⟩
  have hp' : p.map (algebraMap A B) ≠ ⊥ :=
    (Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective A B)).not.mpr hp
  have hPbot : P ≠ ⊥ := by
    rintro rfl
    exact he0 (Ideal.ramificationIdx_bot' hp (FaithfulSMul.algebraMap_injective A B))
  obtain ⟨Q, hPQ, hQ⟩ := Ideal.eq_prime_pow_mul_coprime hp' P
  rw [← IsDedekindDomain.ramificationIdx'_eq_normalizedFactors_count hp' inferInstance hPbot]
    at hQ
  have hcop : IsCoprime (P ^ ramificationIdx' p P) Q :=
    (Ideal.isCoprime_iff_sup_eq.mpr hPQ).pow_left
  letI : Algebra (A ⧸ p) (B ⧸ Q) := Ideal.Quotient.algebraQuotientOfLEComap (by
      rw [← Ideal.map_le_iff_le_comap, hQ]
      exact Ideal.mul_le_right)
  have : IsScalarTower A (A ⧸ p) (B ⧸ Q) := .of_algebraMap_eq' rfl
  have : Module.Finite (A ⧸ p) (B ⧸ Q) :=
    Module.Finite.of_restrictScalars_finite A (A ⧸ p) (B ⧸ Q)
  have : IsScalarTower A (A ⧸ p) (B ⧸ P ^ ramificationIdx' p P) := .of_algebraMap_eq' rfl
  have : Module.Finite (A ⧸ p) (B ⧸ P ^ ramificationIdx' p P) :=
    Module.Finite.of_restrictScalars_finite A (A ⧸ p) _
  have : Module.Finite (A ⧸ p) (B ⧸ P) :=
    Module.Finite.of_restrictScalars_finite A (A ⧸ p) _
  let crt : (B ⧸ p.map (algebraMap A B)) ≃ₐ[A ⧸ p]
      ((B ⧸ P ^ ramificationIdx' p P) × B ⧸ Q) :=
    { __ := (Ideal.quotEquivOfEq hQ).trans
        (Ideal.quotientMulEquivQuotientProd (P ^ ramificationIdx' p P) Q hcop),
      commutes' := Quotient.ind fun _ ↦ rfl }
  obtain ⟨x, hx⟩ :
      ∃ x : B, Algebra.trace (A ⧸ p) (B ⧸ P) (Ideal.Quotient.mk P x) ≠ 0 := by
    obtain ⟨y, hy⟩ : ∃ y, Algebra.trace (A ⧸ p) (B ⧸ P) y ≠ 0 := by
      simpa [LinearMap.ext_iff] using Algebra.trace_ne_zero (A ⧸ p) (B ⧸ P)
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact ⟨x, hy⟩
  have hx' : Algebra.trace (A ⧸ p) (B ⧸ P ^ ramificationIdx' p P)
      (Ideal.Quotient.mk _ x) ≠ 0 := by
    rw [Ideal.trace_quotient_pow_ramificationIdx p P hPbot x, nsmul_eq_mul]
    exact mul_ne_zero he hx
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (crt.symm (Ideal.Quotient.mk _ x, 0))
  refine not_dvd_differentIdeal_of_intTrace_not_mem A (P ^ ramificationIdx' p P) Q hQ.symm
    y ?_ ?_
  · have := congr((crt $hy).2)
    simp at this
    simpa [crt, Ideal.Quotient.eq_zero_iff_mem] using this
  · rw [← Ideal.Quotient.eq_zero_iff_mem, ← Algebra.trace_quotient_eq_of_isDedekindDomain,
      hy, Algebra.trace_eq_of_algEquiv, Algebra.trace_prod_apply]
    simpa using hx'

theorem emultiplicity_differentIdeal_eq_ramificationIdx_sub_one {p : Ideal A} [p.IsMaximal]
    (hp : p ≠ ⊥) (P : Ideal B) [P.IsMaximal] [P.LiesOver p]
    [Algebra.IsSeparable (A ⧸ p) (B ⧸ P)] (he : ((ramificationIdx' p P : ℕ) : A ⧸ p) ≠ 0) :
    emultiplicity P (differentIdeal A B) = (ramificationIdx' p P - 1 : ℕ) := by
  have he0 : ramificationIdx' p P ≠ 0 := by
    rintro h
    simp [h] at he
  rw [emultiplicity_eq_coe, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr he0)]
  exact ⟨pow_sub_one_dvd_differentIdeal A P _ hp (Ideal.dvd_iff_le.mpr le_pow_ramificationIdx),
    not_pow_ramificationIdx_dvd_differentIdeal A hp P he⟩

theorem count_normalizedFactors_differentIdeal_eq_ramificationIdx_sub_one [DecidableEq (Ideal B)]
    {p : Ideal A} [p.IsMaximal] (hp : p ≠ ⊥) (P : Ideal B) [P.IsMaximal] [P.LiesOver p]
    [Algebra.IsSeparable (A ⧸ p) (B ⧸ P)] (he : ((ramificationIdx' p P : ℕ) : A ⧸ p) ≠ 0) :
    (normalizedFactors (differentIdeal A B)).count P = ramificationIdx' p P - 1 := by
  have hPbot : P ≠ ⊥ := by
    rintro rfl
    apply he
    rw [Ideal.ramificationIdx_bot' hp (FaithfulSMul.algebraMap_injective A B), Nat.cast_zero]
  have := emultiplicity_differentIdeal_eq_ramificationIdx_sub_one A hp P he
  rw [emultiplicity_eq_count_normalizedFactors
    ((Ideal.prime_iff_isPrime hPbot).mpr inferInstance).irreducible differentIdeal_ne_bot,
    normalize_eq, Nat.cast_inj] at this
  exact this

theorem not_pow_ramificationIdx_dvd_differentIdeal_of_finite {p : Ideal A} [p.IsMaximal]
    [Finite (A ⧸ p)] (hp : p ≠ ⊥) (P : Ideal B) [P.IsMaximal] [P.LiesOver p]
    (he : ((ramificationIdx' p P : ℕ) : A ⧸ p) ≠ 0) :
    ¬ P ^ ramificationIdx' p P ∣ differentIdeal A B :=
  not_pow_ramificationIdx_dvd_differentIdeal A hp P he

theorem count_normalizedFactors_differentIdeal_eq_ramificationIdx_sub_one_of_finite
    [DecidableEq (Ideal B)] {p : Ideal A} [p.IsMaximal] [Finite (A ⧸ p)] (hp : p ≠ ⊥)
    (P : Ideal B) [P.IsMaximal] [P.LiesOver p]
    (he : ((ramificationIdx' p P : ℕ) : A ⧸ p) ≠ 0) :
    (normalizedFactors (differentIdeal A B)).count P = ramificationIdx' p P - 1 :=
  count_normalizedFactors_differentIdeal_eq_ramificationIdx_sub_one A hp P he

end TameDifferent
p2m_reactivate "P2MW.S_WeierstrassCurve_card_range_galoisRep_three_le_two.B6Inertia P2MW.S_WeierstrassCurve_card_range_galoisRep_three_le_two.ValuationSubring P2MW.S_WeierstrassCurve_card_range_galoisRep_three_le_two.Ideal"

section MinkowskiKill

p2m_open "NumberField P2MW.S_WeierstrassCurve_card_range_galoisRep_three_le_two.NumberField Ideal P2MW.S_WeierstrassCurve_card_range_galoisRep_three_le_two.Ideal NumberField.Ideal UniqueFactorizationMonoid"

attribute [local instance] Ideal.Quotient.field FractionRing.liftAlgebra
  FractionRing.isScalarTower_liftAlgebra

theorem nine_mul_pow_lt_four_mul_pow {m : ℕ} (hm : 2 ≤ m) : 9 * 48 ^ m < 4 * 81 ^ m := by
  induction m, hm using Nat.le_induction with
  | base => norm_num
  | succ m _ ih =>
    calc 9 * 48 ^ (m + 1) = 48 * (9 * 48 ^ m) := by ring
      _ < 48 * (4 * 81 ^ m) := by gcongr
      _ ≤ 81 * (4 * 81 ^ m) := by gcongr; norm_num
      _ = 4 * 81 ^ (m + 1) := by ring

namespace NumberField p2m_export "NumberField" "abs_discr_ge IsTotallyComplex IsTotallyComplex.finrank discr of_module_finite mk place RingOfIntegers.not_isField to_finiteDimensional RingOfIntegers InfinitePlace.not_isReal_iff_isComplex InfinitePlace.nrComplexPlaces RingOfIntegers.coe_injective InfinitePlace.isReal_iff InfinitePlace absNorm_differentIdeal to_charZero RingOfIntegers.rank RingOfIntegers.isIntegral_coe" end NumberField
p2m_open_scoped "NumberField" in

theorem NumberField.differentIdeal_sq_dvd_span_three (M : Type*) [Field M] [NumberField M]
    (h_unram : ∀ (P : Ideal (𝓞 M)) [P.IsMaximal], (3 : 𝓞 M) ∉ P →
      Algebra.IsUnramifiedAt ℤ P)
    (h_tame : ∀ (P : Ideal (𝓞 M)) [P.IsMaximal], (3 : 𝓞 M) ∈ P →
      ramificationIdx' (Ideal.span {(3 : ℤ)}) P ≤ 2) :
    differentIdeal ℤ (𝓞 M) ^ 2 ∣ (Ideal.span {(3 : ℤ)}).map (algebraMap ℤ (𝓞 M)) := by
  classical
  set p : Ideal ℤ := Ideal.span {(3 : ℤ)} with hp_def
  have hp : p ≠ ⊥ := by simp [p]
  haveI : p.IsMaximal := Int.prime_three.isMaximal_span_singleton
  haveI : Finite (ℤ ⧸ p) := Ideal.finiteQuotientOfFreeOfNeBot p hp
  have hJ : p.map (algebraMap ℤ (𝓞 M)) ≠ ⊥ :=
    (Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective ℤ (𝓞 M))).not.mpr hp
  have hD : differentIdeal ℤ (𝓞 M) ≠ ⊥ := differentIdeal_ne_bot
  rw [dvd_iff_normalizedFactors_le_normalizedFactors (pow_ne_zero _ hD) hJ,
    Multiset.le_iff_count, normalizedFactors_pow]
  intro P
  rw [Multiset.count_nsmul]
  by_cases hPmem : P ∈ normalizedFactors (differentIdeal ℤ (𝓞 M))
  swap
  · rw [Multiset.count_eq_zero_of_notMem hPmem, mul_zero]
    exact Nat.zero_le _
  have hPprime : P.IsPrime := isPrime_of_prime (prime_of_normalized_factor P hPmem)
  have hP0 : P ≠ ⊥ := (prime_of_normalized_factor P hPmem).ne_zero
  haveI : P.IsMaximal := hPprime.isMaximal hP0
  by_cases h3 : (3 : 𝓞 M) ∈ P
  ·
    haveI : P.LiesOver p := (Ideal.liesOver_span_iff hPprime.ne_top Int.prime_three).mpr
      (by simpa using h3)
    have he0 : ramificationIdx' p P ≠ 0 :=
      IsDedekindDomain.ramificationIdx_ne_zero_of_liesOver P hp
    have he2 : ramificationIdx' p P ≤ 2 := h_tame P h3
    have he : ((ramificationIdx' p P : ℕ) : ℤ ⧸ p) ≠ 0 := by
      rw [← map_natCast (Ideal.Quotient.mk p), Ne, Ideal.Quotient.eq_zero_iff_mem,
        Ideal.mem_span_singleton]
      omega
    rw [count_normalizedFactors_differentIdeal_eq_ramificationIdx_sub_one ℤ hp P he,
      ← IsDedekindDomain.ramificationIdx'_eq_normalizedFactors_count hJ hPprime hP0]
    omega
  ·
    have hnd : ¬ P ∣ differentIdeal ℤ (𝓞 M) := not_dvd_differentIdeal_iff.mpr (h_unram P h3)
    exact absurd (dvd_of_mem_normalizedFactors hPmem) hnd

p2m_open_scoped "NumberField" in

theorem NumberField.natAbs_discr_sq_dvd_three_pow (M : Type*) [Field M] [NumberField M]
    (h_unram : ∀ (P : Ideal (𝓞 M)) [P.IsMaximal], (3 : 𝓞 M) ∉ P →
      Algebra.IsUnramifiedAt ℤ P)
    (h_tame : ∀ (P : Ideal (𝓞 M)) [P.IsMaximal], (3 : 𝓞 M) ∈ P →
      ramificationIdx' (Ideal.span {(3 : ℤ)}) P ≤ 2) :
    (discr M).natAbs ^ 2 ∣ 3 ^ Module.finrank ℚ M := by
  have h := Ideal.absNorm_dvd_absNorm_of_le
    (Ideal.le_of_dvd (differentIdeal_sq_dvd_span_three M h_unram h_tame))
  rw [map_pow, absNorm_differentIdeal M, Ideal.map_span, Set.image_singleton,
    Ideal.absNorm_span_singleton, Algebra.norm_algebraMap, RingOfIntegers.rank] at h
  simpa using h

p2m_open_scoped "NumberField" in

theorem NumberField.finrank_le_two_of_unramified_outside_three_of_tame (M : Type*) [Field M]
    [NumberField M] [IsTotallyComplex M]
    (h_unram : ∀ (P : Ideal (𝓞 M)) [P.IsMaximal], (3 : 𝓞 M) ∉ P →
      Algebra.IsUnramifiedAt ℤ P)
    (h_tame : ∀ (P : Ideal (𝓞 M)) [P.IsMaximal], (3 : 𝓞 M) ∈ P →
      ramificationIdx' (Ideal.span {(3 : ℤ)}) P ≤ 2) :
    Module.finrank ℚ M ≤ 2 := by
  by_contra! hn
  set m := InfinitePlace.nrComplexPlaces M with hm_def
  have hnm : Module.finrank ℚ M = 2 * m := IsTotallyComplex.finrank M
  have hm : 2 ≤ m := by omega

  have hdvd := natAbs_discr_sq_dvd_three_pow M h_unram h_tame
  rw [hnm, mul_comm, pow_mul] at hdvd
  have hle : (discr M).natAbs ^ 2 ≤ (3 ^ m) ^ 2 := Nat.le_of_dvd (by positivity) hdvd
  have hle' : (discr M).natAbs ≤ 3 ^ m := (Nat.pow_le_pow_iff_left two_ne_zero).mp hle
  have hreal : ((|discr M| : ℤ) : ℝ) ≤ (3 : ℝ) ^ m := by
    rw [← Int.natCast_natAbs]
    exact_mod_cast hle'

  have hmink := abs_discr_ge (K := M) (by omega)
  rw [hnm] at hmink
  have hπ : (81 / 16 : ℝ) ≤ (3 * Real.pi / 4) ^ 2 := by
    have h3 : (9 / 4 : ℝ) ≤ 3 * Real.pi / 4 := by linarith [Real.pi_gt_three]
    nlinarith [h3]
  have key : (4 / 9 : ℝ) * (81 / 16) ^ m ≤ (3 : ℝ) ^ m := by
    calc (4 / 9 : ℝ) * (81 / 16) ^ m ≤ (4 / 9) * ((3 * Real.pi / 4) ^ 2) ^ m := by gcongr
      _ = (4 / 9) * (3 * Real.pi / 4) ^ (2 * m) := by rw [pow_mul]
      _ ≤ ((|discr M| : ℤ) : ℝ) := hmink
      _ ≤ 3 ^ m := hreal

  have key' : (4 : ℝ) * 81 ^ m ≤ 9 * 48 ^ m := by
    have := mul_le_mul_of_nonneg_right key (by positivity : (0 : ℝ) ≤ 9 * 16 ^ m)
    calc (4 : ℝ) * 81 ^ m = (4 / 9 * (81 / 16) ^ m) * (9 * 16 ^ m) := by
            rw [div_pow]; field_simp
      _ ≤ 3 ^ m * (9 * 16 ^ m) := this
      _ = 9 * 48 ^ m := by rw [show (48 : ℝ) = 3 * 16 by norm_num, mul_pow]; ring
  have := nine_mul_pow_lt_four_mul_pow hm
  have : ((9 * 48 ^ m : ℕ) : ℝ) < ((4 * 81 ^ m : ℕ) : ℝ) := by exact_mod_cast this
  push_cast at this
  linarith

end MinkowskiKill
p2m_reactivate "P2MW.S_WeierstrassCurve_card_range_galoisRep_three_le_two.B6Inertia P2MW.S_WeierstrassCurve_card_range_galoisRep_three_le_two.ValuationSubring P2MW.S_WeierstrassCurve_card_range_galoisRep_three_le_two.Ideal"

namespace B6P3

p2m_open "NumberField P2MW.S_WeierstrassCurve_card_range_galoisRep_three_le_two.NumberField"

theorem isTotallyComplex_of_exists_cube_root {M : Type*} [Field M]
    (hζ : ∃ ζ : M, ζ ^ 2 + ζ + 1 = 0) : IsTotallyComplex M := by
  obtain ⟨ζ, hζ⟩ := hζ
  refine ⟨fun w => ?_⟩
  rw [← InfinitePlace.not_isReal_iff_isComplex, InfinitePlace.isReal_iff]
  intro hw
  have h := congrArg hw.embedding hζ
  simp only [map_add, map_pow, map_one, map_zero] at h
  nlinarith [sq_nonneg (2 * hw.embedding ζ + 1)]

theorem exists_prime_natCast_mem {M : Type*} [Field M] [NumberField M] (P : Ideal (𝓞 M))
    [hP : P.IsMaximal] : ∃ q : ℕ, q.Prime ∧ (q : 𝓞 M) ∈ P := by
  have hP0 : P ≠ ⊥ :=
    Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField M)
  haveI : Finite (𝓞 M ⧸ P) := Ideal.finiteQuotientOfFreeOfNeBot P hP0
  letI := Ideal.Quotient.field P
  obtain ⟨q, hq⟩ := CharP.exists (𝓞 M ⧸ P)
  refine ⟨q, CharP.char_is_prime (𝓞 M ⧸ P) q, ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
  exact CharP.cast_eq_zero _ q

theorem finrank_le_two_of_inertia_le (L : IntermediateField ℚ (AlgebraicClosure ℚ))
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (hunr : ∀ q : ℕ, q.Prime → q ≠ 3 → ∀ A : ValuationSubring (AlgebraicClosure ℚ),
      A.LiesOverPrime q → (A.inertiaSubgroupIn ℚ).map (AlgEquiv.restrictNormalHom L) = ⊥)
    (htame : ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime 3 →
      Nat.card ((A.inertiaSubgroupIn ℚ).map (AlgEquiv.restrictNormalHom L)) ≤ 2)
    (hζ : ∃ ζ : L, ζ ^ 2 + ζ + 1 = 0) :
    Module.finrank ℚ L ≤ 2 := by
  haveI : IsTotallyComplex L := isTotallyComplex_of_exists_cube_root hζ
  refine NumberField.finrank_le_two_of_unramified_outside_three_of_tame L ?_ ?_
  ·
    intro P _ h3
    obtain ⟨q, hq, hqP⟩ := exists_prime_natCast_mem P
    have hq3 : q ≠ 3 := by
      rintro rfl
      exact h3 (by simpa using hqP)
    obtain ⟨A, hA, hAP⟩ := ValuationSubring.exists_liesOverPrime_primeBelow_eq L P hqP
    have h := (A.map_restrictNormalHom_inertiaSubgroupIn_eq_bot_iff_isUnramifiedAt L hq hA).mp
      (hunr q hq hq3 A hA)
    subst hAP
    exact h
  ·
    intro P _ h3
    obtain ⟨A, hA, hAP⟩ :=
      ValuationSubring.exists_liesOverPrime_primeBelow_eq L P (p := 3) (by simpa using h3)
    have hcard := A.card_map_restrictNormalHom_inertiaSubgroupIn L Nat.prime_three hA
    rw [hAP] at hcard
    have h := htame A hA
    rw [hcard] at h
    simpa using h

theorem card_aut_le_two_of_inertia_le (L : IntermediateField ℚ (AlgebraicClosure ℚ))
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (hunr : ∀ q : ℕ, q.Prime → q ≠ 3 → ∀ A : ValuationSubring (AlgebraicClosure ℚ),
      A.LiesOverPrime q → (A.inertiaSubgroupIn ℚ).map (AlgEquiv.restrictNormalHom L) = ⊥)
    (htame : ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime 3 →
      Nat.card ((A.inertiaSubgroupIn ℚ).map (AlgEquiv.restrictNormalHom L)) ≤ 2)
    (hζ : ∃ ζ : L, ζ ^ 2 + ζ + 1 = 0) :
    Nat.card (L ≃ₐ[ℚ] L) ≤ 2 := by
  rw [IsGalois.card_aut_eq_finrank]
  exact finrank_le_two_of_inertia_le L hunr htame hζ

end B6P3
p2m_reactivate "P2MW.S_WeierstrassCurve_card_range_galoisRep_three_le_two.B6Inertia P2MW.S_WeierstrassCurve_card_range_galoisRep_three_le_two.ValuationSubring P2MW.S_WeierstrassCurve_card_range_galoisRep_three_le_two.Ideal"

set_option autoImplicit false

noncomputable section

p2m_open_scoped "WeierstrassCurve.Affine P2MW.S_WeierstrassCurve_card_range_galoisRep_three_le_two.WeierstrassCurve.Affine"
open IntermediateField

attribute [local instance 1100] IntermediateField.algebra' IntermediateField.module'

namespace AlgebraicClosure
p2m_export "AlgebraicClosure" "isAlgebraic instAlgebra"
p2m_open "AlgebraicClosure"

scoped instance isAlgebraic_rat : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) :=
  AlgebraicClosure.isAlgebraic ℚ

scoped instance isAlgClosure_rat : IsAlgClosure ℚ (AlgebraicClosure ℚ) :=
  ⟨inferInstance, inferInstance⟩

scoped instance normal_rat : Normal ℚ (AlgebraicClosure ℚ) :=
  IsAlgClosure.normal ℚ (AlgebraicClosure ℚ)

scoped instance isGalois_rat : IsGalois ℚ (AlgebraicClosure ℚ) :=
  IsAlgClosure.isGalois ℚ (AlgebraicClosure ℚ)

end AlgebraicClosure
p2m_reactivate "P2MW.S_WeierstrassCurve_card_range_galoisRep_three_le_two.B6Inertia P2MW.S_WeierstrassCurve_card_range_galoisRep_three_le_two.ValuationSubring P2MW.S_WeierstrassCurve_card_range_galoisRep_three_le_two.Ideal P2MW.S_WeierstrassCurve_card_range_galoisRep_three_le_two.AlgebraicClosure"

namespace ResidualGaloisRep
p2m_export "ResidualGaloisRep" "IsUnramifiedAt V ρ mk"
p2m_open "ResidualGaloisRep"

theorem monoidHom_apply_eq_apply_iff_inv_mul_mem_ker {G M : Type*} [Group G] [Monoid M]
    (f : G →* M) (a b : G) : f a = f b ↔ a⁻¹ * b ∈ f.ker := by
  rw [MonoidHom.mem_ker]
  constructor
  · intro h
    rw [map_mul, ← h, ← map_mul, inv_mul_cancel, map_one]
  · intro h
    calc f a = f a * f (a⁻¹ * b) := by rw [h, mul_one]
      _ = f b := by rw [← map_mul, mul_inv_cancel_left]

theorem natCard_image_eq_of_apply_eq_iff {α β γ : Type*} (f : α → β) (g : α → γ)
    (h : ∀ a b, f a = f b ↔ g a = g b) (T : Set α) : Nat.card (f '' T) = Nat.card (g '' T) := by
  classical
  refine Nat.card_congr (Equiv.ofBijective
    (fun y => ⟨g (Classical.choose y.2), Set.mem_image_of_mem g (Classical.choose_spec y.2).1⟩)
    ⟨?_, ?_⟩)
  · rintro ⟨y₁, hy₁⟩ ⟨y₂, hy₂⟩ hg
    have hg' : g (Classical.choose hy₁) = g (Classical.choose hy₂) := congrArg Subtype.val hg
    apply Subtype.ext
    change y₁ = y₂
    rw [← (Classical.choose_spec hy₁).2, ← (Classical.choose_spec hy₂).2]
    exact (h _ _).mpr hg'
  · rintro ⟨_, b, hb, rfl⟩
    refine ⟨⟨f b, Set.mem_image_of_mem f hb⟩, Subtype.ext ?_⟩
    exact (h _ _).mp (Classical.choose_spec (Set.mem_image_of_mem f hb)).2

section Level

variable (S : Set (AlgebraicClosure ℚ)) {k : Type} [Field k] (ρ : ResidualGaloisRep k)

local notation "Γ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

theorem finiteDimensional_adjoin_of_finite (hfin : S.Finite) :
    FiniteDimensional ℚ (adjoin ℚ S) :=
  haveI : Finite S := hfin.to_subtype
  IntermediateField.finiteDimensional_adjoin
    fun z _ => (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) z).isIntegral

theorem normal_adjoin_of_forall_apply_mem (hstab : ∀ σ : Γ, ∀ z ∈ S, σ z ∈ S) :
    Normal ℚ (adjoin ℚ S) := by
  refine IntermediateField.normal_iff_forall_map_le'.mpr fun σ => ?_
  rw [adjoin_map]
  exact adjoin.mono ℚ _ _ (Set.image_subset_iff.mpr fun z hz => hstab σ z hz)

theorem isGalois_adjoin [Normal ℚ (adjoin ℚ S)] : IsGalois ℚ (adjoin ℚ S) := ⟨⟩

theorem adjoin_le_fixedField_ker (hρ : ∀ σ : Γ, (∀ z ∈ S, σ z = z) ↔ ρ.ρ σ = 1) :
    adjoin ℚ S ≤ fixedField ρ.ρ.ker :=
  adjoin_le_iff.mpr fun z hz => (mem_fixedField_iff _ z).mpr
    fun τ hτ => (hρ τ).mpr ((MonoidHom.mem_ker).mp hτ) z hz

theorem forall_mem_adjoin_apply_eq_self_iff (hρ : ∀ σ : Γ, (∀ z ∈ S, σ z = z) ↔ ρ.ρ σ = 1)
    (σ : Γ) : (∀ z ∈ adjoin ℚ S, σ z = z) ↔ ρ.ρ σ = 1 := by
  constructor
  · exact fun h => (hρ σ).mp fun z hz => h z (subset_adjoin ℚ S hz)
  · intro h z hz
    exact (mem_fixedField_iff _ z).mp (adjoin_le_fixedField_ker S ρ hρ hz) σ
      ((MonoidHom.mem_ker).mpr h)

theorem fixingSubgroup_adjoin_eq_ker (hρ : ∀ σ : Γ, (∀ z ∈ S, σ z = z) ↔ ρ.ρ σ = 1) :
    (adjoin ℚ S).fixingSubgroup = ρ.ρ.ker :=
  Subgroup.ext fun σ => by
    rw [IntermediateField.mem_fixingSubgroup_iff, MonoidHom.mem_ker]
    exact forall_mem_adjoin_apply_eq_self_iff S ρ hρ σ

theorem mem_fixingSubgroup_adjoin_iff (hρ : ∀ σ : Γ, (∀ z ∈ S, σ z = z) ↔ ρ.ρ σ = 1)
    (σ : Γ) : σ ∈ (adjoin ℚ S).fixingSubgroup ↔ ρ.ρ σ = 1 := by
  rw [fixingSubgroup_adjoin_eq_ker S ρ hρ, MonoidHom.mem_ker]

theorem restrictNormalHom_ker_eq [Normal ℚ (adjoin ℚ S)]
    (hρ : ∀ σ : Γ, (∀ z ∈ S, σ z = z) ↔ ρ.ρ σ = 1) :
    (AlgEquiv.restrictNormalHom (adjoin ℚ S) :
      Γ →* (adjoin ℚ S ≃ₐ[ℚ] adjoin ℚ S)).ker = ρ.ρ.ker :=
  (IntermediateField.restrictNormalHom_ker (adjoin ℚ S)).trans
    (fixingSubgroup_adjoin_eq_ker S ρ hρ)

theorem restrictNormalHom_apply_eq_iff [Normal ℚ (adjoin ℚ S)]
    (hρ : ∀ σ : Γ, (∀ z ∈ S, σ z = z) ↔ ρ.ρ σ = 1) (σ τ : Γ) :
    AlgEquiv.restrictNormalHom (adjoin ℚ S) σ = AlgEquiv.restrictNormalHom (adjoin ℚ S) τ ↔
      ρ.ρ σ = ρ.ρ τ := by
  rw [monoidHom_apply_eq_apply_iff_inv_mul_mem_ker, monoidHom_apply_eq_apply_iff_inv_mul_mem_ker,
    restrictNormalHom_ker_eq S ρ hρ]

theorem natCard_image_eq_natCard_map [Normal ℚ (adjoin ℚ S)]
    (hρ : ∀ σ : Γ, (∀ z ∈ S, σ z = z) ↔ ρ.ρ σ = 1) (I : Subgroup Γ) :
    Nat.card (ρ.ρ '' (I : Set Γ)) =
      Nat.card (I.map (AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := AlgebraicClosure ℚ)
        (adjoin ℚ S))) := by
  rw [← SetLike.coe_sort_coe (I.map _), Subgroup.coe_map]
  exact natCard_image_eq_of_apply_eq_iff _ _
    (fun a b => (restrictNormalHom_apply_eq_iff S ρ hρ a b).symm) _

theorem natCard_range_eq_finrank [FiniteDimensional ℚ (adjoin ℚ S)] [Normal ℚ (adjoin ℚ S)]
    (hρ : ∀ σ : Γ, (∀ z ∈ S, σ z = z) ↔ ρ.ρ σ = 1) :
    Nat.card (Set.range ρ.ρ) = Module.finrank ℚ (adjoin ℚ S) := by
  haveI : IsGalois ℚ (adjoin ℚ S) := isGalois_adjoin S
  have h1 : Nat.card (Set.range ρ.ρ) =
      Nat.card (Set.range (AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := AlgebraicClosure ℚ)
        (adjoin ℚ S))) := by
    rw [← Set.image_univ, ← Set.image_univ]
    exact natCard_image_eq_of_apply_eq_iff _ _
      (fun a b => (restrictNormalHom_apply_eq_iff S ρ hρ a b).symm) _
  rw [h1, Set.range_eq_univ.mpr (AlgEquiv.restrictNormalHom_surjective (F := ℚ)
    (E := AlgebraicClosure ℚ) (K₁ := adjoin ℚ S)), Nat.card_univ, IsGalois.card_aut_eq_finrank]

theorem mem_adjoin_of_forall_ker (hρ : ∀ σ : Γ, (∀ z ∈ S, σ z = z) ↔ ρ.ρ σ = 1)
    (ζ : AlgebraicClosure ℚ) (h : ∀ σ : Γ, ρ.ρ σ = 1 → σ ζ = ζ) : ζ ∈ adjoin ℚ S := by
  rw [← InfiniteGalois.fixedField_fixingSubgroup (adjoin ℚ S), mem_fixedField_iff,
    fixingSubgroup_adjoin_eq_ker S ρ hρ]
  exact fun σ hσ => h σ ((MonoidHom.mem_ker).mp hσ)

omit ρ in

theorem numberField_adjoin [FiniteDimensional ℚ (adjoin ℚ S)] : NumberField (adjoin ℚ S) :=
  NumberField.of_module_finite ℚ (adjoin ℚ S)

end Level
p2m_reactivate "P2MW.S_WeierstrassCurve_card_range_galoisRep_three_le_two.B6Inertia P2MW.S_WeierstrassCurve_card_range_galoisRep_three_le_two.ValuationSubring P2MW.S_WeierstrassCurve_card_range_galoisRep_three_le_two.Ideal P2MW.S_WeierstrassCurve_card_range_galoisRep_three_le_two.AlgebraicClosure"

end ResidualGaloisRep
p2m_reactivate "P2MW.S_WeierstrassCurve_card_range_galoisRep_three_le_two.B6Inertia P2MW.S_WeierstrassCurve_card_range_galoisRep_three_le_two.ValuationSubring P2MW.S_WeierstrassCurve_card_range_galoisRep_three_le_two.Ideal P2MW.S_WeierstrassCurve_card_range_galoisRep_three_le_two.AlgebraicClosure"

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine map mk isIntegral_iff IsIntegral Affine.Point Δ residualGaloisRepOf Affine.Point.galoisRepModuleEnd card apply_eq_self_of_galoisRep_eq_one_of_pow_eq_one"
namespace Affine
p2m_export "WeierstrassCurve.Affine" "map Point.some Nonsingular Point Point.galoisRepModuleEnd"
namespace Point
p2m_export "WeierstrassCurve.Affine.Point" "some some.injEq map_zero map map_some zero mk algEquiv_smul_def algEquiv_smul_zsmul galoisRepModuleEnd"
p2m_open "WeierstrassCurve.Affine.Point WeierstrassCurve.Affine WeierstrassCurve"

section Coords

variable {R : Type*} [CommRing R] {W : Affine R}

private def _root_.WeierstrassCurve.Affine.Point.coords : W.Point → Set R
  | .zero => ∅
  | .some x y _ => {x, y}

p2m_export "WeierstrassCurve.Affine.Point" "coords"
@[scoped simp] theorem coords_zero : coords (0 : W.Point) = ∅ := rfl

@[scoped simp] theorem coords_some {x y : R} (h : W.Nonsingular x y) :
    coords (Point.some x y h) = {x, y} := rfl

theorem coords_finite (P : W.Point) : (coords P).Finite := by
  cases P with
  | zero => exact Set.finite_empty
  | some x y h => exact (Set.finite_singleton y).insert x

end Coords
p2m_reactivate "P2MW.S_WeierstrassCurve_card_range_galoisRep_three_le_two.B6Inertia P2MW.S_WeierstrassCurve_card_range_galoisRep_three_le_two.ValuationSubring P2MW.S_WeierstrassCurve_card_range_galoisRep_three_le_two.Ideal P2MW.S_WeierstrassCurve_card_range_galoisRep_three_le_two.AlgebraicClosure"

section Galois

variable {R S K : Type*} [CommRing R] [CommRing S] [Field K] [DecidableEq K] {W' : Affine R}
  [Algebra R S] [Algebra R K] [Algebra S K] [IsScalarTower R S K]

theorem coords_smul (σ : K ≃ₐ[S] K) (P : (W'⁄K).Point) : coords (σ • P) = σ '' coords P := by
  cases P with
  | zero => exact (Set.image_empty σ).symm
  | some x y h =>
    rw [algEquiv_smul_def, map_some, coords_some, coords_some, Set.image_insert_eq,
      Set.image_singleton]
    rfl

theorem smul_eq_self_iff_forall_coords (σ : K ≃ₐ[S] K) (P : (W'⁄K).Point) :
    σ • P = P ↔ ∀ z ∈ coords P, σ z = z := by
  cases P with
  | zero => exact ⟨fun _ z hz => hz.elim, fun _ => rfl⟩
  | some x y h =>
    rw [algEquiv_smul_def, map_some, coords_some]
    simp only [some.injEq, Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp,
      forall_eq]
    rfl

end Galois
p2m_reactivate "P2MW.S_WeierstrassCurve_card_range_galoisRep_three_le_two.B6Inertia P2MW.S_WeierstrassCurve_card_range_galoisRep_three_le_two.ValuationSubring P2MW.S_WeierstrassCurve_card_range_galoisRep_three_le_two.Ideal P2MW.S_WeierstrassCurve_card_range_galoisRep_three_le_two.AlgebraicClosure"

end WeierstrassCurve.Affine.Point
p2m_reactivate "P2MW.S_WeierstrassCurve_card_range_galoisRep_three_le_two.B6Inertia P2MW.S_WeierstrassCurve_card_range_galoisRep_three_le_two.ValuationSubring P2MW.S_WeierstrassCurve_card_range_galoisRep_three_le_two.Ideal P2MW.S_WeierstrassCurve_card_range_galoisRep_three_le_two.AlgebraicClosure P2MW.S_WeierstrassCurve_card_range_galoisRep_three_le_two.WeierstrassCurve P2MW.S_WeierstrassCurve_card_range_galoisRep_three_le_two.WeierstrassCurve.Affine P2MW.S_WeierstrassCurve_card_range_galoisRep_three_le_two.WeierstrassCurve.Affine.Point"
p2m_reactivate "P2MW.S_WeierstrassCurve_card_range_galoisRep_three_le_two.B6Inertia P2MW.S_WeierstrassCurve_card_range_galoisRep_three_le_two.ValuationSubring P2MW.S_WeierstrassCurve_card_range_galoisRep_three_le_two.Ideal P2MW.S_WeierstrassCurve_card_range_galoisRep_three_le_two.AlgebraicClosure P2MW.S_WeierstrassCurve_card_range_galoisRep_three_le_two.WeierstrassCurve P2MW.S_WeierstrassCurve_card_range_galoisRep_three_le_two.WeierstrassCurve.Affine"
p2m_reactivate "P2MW.S_WeierstrassCurve_card_range_galoisRep_three_le_two.B6Inertia P2MW.S_WeierstrassCurve_card_range_galoisRep_three_le_two.ValuationSubring P2MW.S_WeierstrassCurve_card_range_galoisRep_three_le_two.Ideal P2MW.S_WeierstrassCurve_card_range_galoisRep_three_le_two.AlgebraicClosure P2MW.S_WeierstrassCurve_card_range_galoisRep_three_le_two.WeierstrassCurve"

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine map mk isIntegral_iff IsIntegral Affine.Point Δ residualGaloisRepOf Affine.Point.galoisRepModuleEnd card apply_eq_self_of_galoisRep_eq_one_of_pow_eq_one"
p2m_open "WeierstrassCurve"

p2m_open "WeierstrassCurve.Affine P2MW.S_WeierstrassCurve_card_range_galoisRep_three_le_two.WeierstrassCurve.Affine WeierstrassCurve.Affine.Point P2MW.S_WeierstrassCurve_card_range_galoisRep_three_le_two.WeierstrassCurve.Affine.Point"

variable (E : WeierstrassCurve ℚ) (p : ℕ)

local notation "Γ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

def torsionCoords : Set (AlgebraicClosure ℚ) :=
  ⋃ P ∈ (Submodule.torsionBy ℤ (E⁄(AlgebraicClosure ℚ)).Point p :
    Set (E⁄(AlgebraicClosure ℚ)).Point), P.coords

private abbrev _root_.WeierstrassCurve.torsionField : IntermediateField ℚ (AlgebraicClosure ℚ) :=
  IntermediateField.adjoin ℚ (torsionCoords E p)

p2m_export "WeierstrassCurve" "torsionField"
theorem torsionField_def : torsionField E p = IntermediateField.adjoin ℚ (torsionCoords E p) :=
  rfl

theorem mem_torsionCoords_iff {z : AlgebraicClosure ℚ} :
    z ∈ torsionCoords E p ↔
      ∃ P : (E⁄(AlgebraicClosure ℚ)).Point, (p : ℤ) • P = 0 ∧ z ∈ P.coords := by
  simp only [torsionCoords, Set.mem_iUnion, SetLike.mem_coe, Submodule.mem_torsionBy_iff,
    exists_prop]

theorem mem_torsionCoords_iff' {z : AlgebraicClosure ℚ} :
    z ∈ torsionCoords E p ↔ ∃ (x y : AlgebraicClosure ℚ)
      (h : (E⁄(AlgebraicClosure ℚ)).Nonsingular x y),
        (p : ℤ) • (Point.some x y h) = 0 ∧ (z = x ∨ z = y) := by
  rw [mem_torsionCoords_iff]
  constructor
  · rintro ⟨P, hP, hz⟩
    cases P with
    | zero => exact hz.elim
    | some x y h =>
      exact ⟨x, y, h, hP, by simpa only [coords_some, Set.mem_insert_iff,
        Set.mem_singleton_iff] using hz⟩
  · rintro ⟨x, y, h, hP, hz⟩
    exact ⟨Point.some x y h, hP,
      by simpa only [coords_some, Set.mem_insert_iff, Set.mem_singleton_iff] using hz⟩

theorem mem_torsionField_of_nonsingular {x y : AlgebraicClosure ℚ}
    (h : (E⁄(AlgebraicClosure ℚ)).Nonsingular x y) (hp : (p : ℤ) • (Point.some x y h) = 0) :
    x ∈ torsionField E p ∧ y ∈ torsionField E p :=
  ⟨subset_adjoin ℚ _ ((mem_torsionCoords_iff' E p).mpr ⟨x, y, h, hp, Or.inl rfl⟩),
    subset_adjoin ℚ _ ((mem_torsionCoords_iff' E p).mpr ⟨x, y, h, hp, Or.inr rfl⟩)⟩

theorem torsionCoords_finite [Fact p.Prime]
    (hcard : Nat.card (Submodule.torsionBy ℤ (E⁄(AlgebraicClosure ℚ)).Point p) = p ^ 2) :
    (torsionCoords E p).Finite := by
  haveI : Finite (Submodule.torsionBy ℤ (E⁄(AlgebraicClosure ℚ)).Point p) :=
    Nat.finite_of_card_ne_zero (hcard ▸ pow_ne_zero 2 (Fact.out : p.Prime).pos.ne')
  exact Set.Finite.biUnion (Set.toFinite _) fun P _ => coords_finite P

theorem apply_mem_torsionCoords (σ : Γ) {z : AlgebraicClosure ℚ} (hz : z ∈ torsionCoords E p) :
    σ z ∈ torsionCoords E p := by
  rw [mem_torsionCoords_iff] at hz ⊢
  obtain ⟨P, hP, hz⟩ := hz
  refine ⟨σ • P, ?_, ?_⟩
  · rw [← algEquiv_smul_zsmul, hP, smul_zero]
  · rw [coords_smul]
    exact Set.mem_image_of_mem σ hz

theorem image_torsionCoords_eq (σ : Γ) : σ '' torsionCoords E p = torsionCoords E p := by
  refine Set.Subset.antisymm (Set.image_subset_iff.mpr fun z hz => apply_mem_torsionCoords E p σ hz)
    fun z hz => ⟨σ.symm z, apply_mem_torsionCoords E p σ.symm hz, σ.apply_symm_apply z⟩

namespace torsionField

private scoped instance _root_.WeierstrassCurve.torsionField.normal : Normal ℚ (torsionField E p) :=
  ResidualGaloisRep.normal_adjoin_of_forall_apply_mem _
    fun σ _ hz => apply_mem_torsionCoords E p σ hz

end torsionField
p2m_export "WeierstrassCurve" "torsionField.normal"
p2m_reactivate "P2MW.S_WeierstrassCurve_card_range_galoisRep_three_le_two.B6Inertia P2MW.S_WeierstrassCurve_card_range_galoisRep_three_le_two.ValuationSubring P2MW.S_WeierstrassCurve_card_range_galoisRep_three_le_two.Ideal P2MW.S_WeierstrassCurve_card_range_galoisRep_three_le_two.AlgebraicClosure P2MW.S_WeierstrassCurve_card_range_galoisRep_three_le_two.WeierstrassCurve P2MW.S_WeierstrassCurve_card_range_galoisRep_three_le_two.WeierstrassCurve.Affine P2MW.S_WeierstrassCurve_card_range_galoisRep_three_le_two.WeierstrassCurve.Affine.Point P2MW.S_WeierstrassCurve_card_range_galoisRep_three_le_two.WeierstrassCurve.torsionField"
namespace torsionField

private scoped instance _root_.WeierstrassCurve.torsionField.isGalois : IsGalois ℚ (torsionField E p) :=
  ResidualGaloisRep.isGalois_adjoin _

end torsionField
p2m_export "WeierstrassCurve" "torsionField.isGalois"
p2m_reactivate "P2MW.S_WeierstrassCurve_card_range_galoisRep_three_le_two.B6Inertia P2MW.S_WeierstrassCurve_card_range_galoisRep_three_le_two.ValuationSubring P2MW.S_WeierstrassCurve_card_range_galoisRep_three_le_two.Ideal P2MW.S_WeierstrassCurve_card_range_galoisRep_three_le_two.AlgebraicClosure P2MW.S_WeierstrassCurve_card_range_galoisRep_three_le_two.WeierstrassCurve P2MW.S_WeierstrassCurve_card_range_galoisRep_three_le_two.WeierstrassCurve.Affine P2MW.S_WeierstrassCurve_card_range_galoisRep_three_le_two.WeierstrassCurve.Affine.Point P2MW.S_WeierstrassCurve_card_range_galoisRep_three_le_two.WeierstrassCurve.torsionField"

private theorem _root_.WeierstrassCurve.finiteDimensional_torsionField [Fact p.Prime]
    (hcard : Nat.card (Submodule.torsionBy ℤ (E⁄(AlgebraicClosure ℚ)).Point p) = p ^ 2) :
    FiniteDimensional ℚ (torsionField E p) :=
  ResidualGaloisRep.finiteDimensional_adjoin_of_finite _ (torsionCoords_finite E p hcard)

p2m_export "WeierstrassCurve" "finiteDimensional_torsionField"

theorem numberField_torsionField [Fact p.Prime]
    (hcard : Nat.card (Submodule.torsionBy ℤ (E⁄(AlgebraicClosure ℚ)).Point p) = p ^ 2) :
    NumberField (torsionField E p) :=
  haveI := finiteDimensional_torsionField E p hcard
  ResidualGaloisRep.numberField_adjoin _

theorem forall_torsionCoords_apply_eq_self_iff (σ : Γ) :
    (∀ z ∈ torsionCoords E p, σ z = z) ↔
      galoisRepModuleEnd (K := AlgebraicClosure ℚ) ℚ E p σ = 1 := by
  constructor
  · intro h
    refine LinearMap.ext fun v => Subtype.ext ?_
    change σ • (v : (E⁄(AlgebraicClosure ℚ)).Point) = v
    exact (smul_eq_self_iff_forall_coords σ _).mpr fun z hz => h z
      ((mem_torsionCoords_iff E p).mpr ⟨v, (Submodule.mem_torsionBy_iff _ _).mp v.2, hz⟩)
  · intro h z hz
    obtain ⟨P, hP, hz⟩ := (mem_torsionCoords_iff E p).mp hz
    have hv := LinearMap.congr_fun h ⟨P, (Submodule.mem_torsionBy_iff _ _).mpr hP⟩
    have hP' : σ • P = P := congrArg Subtype.val hv
    exact (smul_eq_self_iff_forall_coords σ P).mp hP' z hz

private theorem _root_.WeierstrassCurve.galoisFactorsThroughFiniteLevel_galoisRepModuleEnd [Fact p.Prime]
    (hcard : Nat.card (Submodule.torsionBy ℤ (E⁄(AlgebraicClosure ℚ)).Point p) = p ^ 2) :
    GaloisFactorsThroughFiniteLevel
      (WeierstrassCurve.Affine.Point.galoisRepModuleEnd (K := AlgebraicClosure ℚ) ℚ E p) :=
  ⟨torsionField E p, finiteDimensional_torsionField E p hcard, fun σ hσ =>
    (forall_torsionCoords_apply_eq_self_iff E p σ).mp fun z hz => hσ z (subset_adjoin ℚ _ hz)⟩

p2m_export "WeierstrassCurve" "galoisFactorsThroughFiniteLevel_galoisRepModuleEnd"
section Rep

variable [Fact p.Prime]
  (hcard : Nat.card (Submodule.torsionBy ℤ (E⁄(AlgebraicClosure ℚ)).Point p) = p ^ 2)
  (hker : GaloisFactorsThroughFiniteLevel
    (WeierstrassCurve.Affine.Point.galoisRepModuleEnd (K := AlgebraicClosure ℚ) ℚ E p))

theorem forall_torsionCoords_apply_eq_self_iff_residualGaloisRepOf (σ : Γ) :
    (∀ z ∈ torsionCoords E p, σ z = z) ↔ (E.residualGaloisRepOf p hcard hker).ρ σ = 1 :=
  forall_torsionCoords_apply_eq_self_iff E p σ

theorem forall_mem_torsionField_apply_eq_self_iff (σ : Γ) :
    (∀ z ∈ torsionField E p, σ z = z) ↔ (E.residualGaloisRepOf p hcard hker).ρ σ = 1 :=
  ResidualGaloisRep.forall_mem_adjoin_apply_eq_self_iff _ _
    (forall_torsionCoords_apply_eq_self_iff_residualGaloisRepOf E p hcard hker) σ

theorem fixingSubgroup_torsionField_eq_ker :
    (torsionField E p).fixingSubgroup = (E.residualGaloisRepOf p hcard hker).ρ.ker :=
  ResidualGaloisRep.fixingSubgroup_adjoin_eq_ker _ _
    (forall_torsionCoords_apply_eq_self_iff_residualGaloisRepOf E p hcard hker)

theorem mem_fixingSubgroup_torsionField_iff (σ : Γ) :
    σ ∈ (torsionField E p).fixingSubgroup ↔ (E.residualGaloisRepOf p hcard hker).ρ σ = 1 :=
  ResidualGaloisRep.mem_fixingSubgroup_adjoin_iff _ _
    (forall_torsionCoords_apply_eq_self_iff_residualGaloisRepOf E p hcard hker) σ

theorem restrictNormalHom_torsionField_ker_eq :
    (AlgEquiv.restrictNormalHom (torsionField E p) :
      Γ →* (torsionField E p ≃ₐ[ℚ] torsionField E p)).ker =
        (E.residualGaloisRepOf p hcard hker).ρ.ker :=
  ResidualGaloisRep.restrictNormalHom_ker_eq _ _
    (forall_torsionCoords_apply_eq_self_iff_residualGaloisRepOf E p hcard hker)

private theorem _root_.WeierstrassCurve.restrictNormalHom_torsionField_apply_eq_iff (σ τ : Γ) :
    AlgEquiv.restrictNormalHom (torsionField E p) σ =
      AlgEquiv.restrictNormalHom (torsionField E p) τ ↔
        (E.residualGaloisRepOf p hcard hker).ρ σ = (E.residualGaloisRepOf p hcard hker).ρ τ :=
  ResidualGaloisRep.restrictNormalHom_apply_eq_iff _ _
    (forall_torsionCoords_apply_eq_self_iff_residualGaloisRepOf E p hcard hker) σ τ

p2m_export "WeierstrassCurve" "restrictNormalHom_torsionField_apply_eq_iff"

private theorem _root_.WeierstrassCurve.natCard_image_residualGaloisRepOf_eq (I : Subgroup Γ) :
    Nat.card ((E.residualGaloisRepOf p hcard hker).ρ '' (I : Set Γ)) =
      Nat.card (I.map (AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := AlgebraicClosure ℚ)
        (torsionField E p))) :=
  ResidualGaloisRep.natCard_image_eq_natCard_map _ _
    (forall_torsionCoords_apply_eq_self_iff_residualGaloisRepOf E p hcard hker) I

p2m_export "WeierstrassCurve" "natCard_image_residualGaloisRepOf_eq"

private theorem _root_.WeierstrassCurve.natCard_range_residualGaloisRepOf_eq_finrank :
    Nat.card (Set.range (E.residualGaloisRepOf p hcard hker).ρ) =
      Module.finrank ℚ (torsionField E p) :=
  haveI := finiteDimensional_torsionField E p hcard
  ResidualGaloisRep.natCard_range_eq_finrank _ _
    (forall_torsionCoords_apply_eq_self_iff_residualGaloisRepOf E p hcard hker)

p2m_export "WeierstrassCurve" "natCard_range_residualGaloisRepOf_eq_finrank"

private theorem _root_.WeierstrassCurve.mem_torsionField_of_forall_ker (ζ : AlgebraicClosure ℚ)
    (h : ∀ σ : Γ, (E.residualGaloisRepOf p hcard hker).ρ σ = 1 → σ ζ = ζ) :
    ζ ∈ torsionField E p :=
  ResidualGaloisRep.mem_adjoin_of_forall_ker _ _
    (forall_torsionCoords_apply_eq_self_iff_residualGaloisRepOf E p hcard hker) ζ h

p2m_export "WeierstrassCurve" "mem_torsionField_of_forall_ker"
end Rep
p2m_reactivate "P2MW.S_WeierstrassCurve_card_range_galoisRep_three_le_two.B6Inertia P2MW.S_WeierstrassCurve_card_range_galoisRep_three_le_two.ValuationSubring P2MW.S_WeierstrassCurve_card_range_galoisRep_three_le_two.Ideal P2MW.S_WeierstrassCurve_card_range_galoisRep_three_le_two.AlgebraicClosure P2MW.S_WeierstrassCurve_card_range_galoisRep_three_le_two.WeierstrassCurve P2MW.S_WeierstrassCurve_card_range_galoisRep_three_le_two.WeierstrassCurve.Affine P2MW.S_WeierstrassCurve_card_range_galoisRep_three_le_two.WeierstrassCurve.Affine.Point P2MW.S_WeierstrassCurve_card_range_galoisRep_three_le_two.WeierstrassCurve.torsionField"

end WeierstrassCurve
p2m_reactivate "P2MW.S_WeierstrassCurve_card_range_galoisRep_three_le_two.B6Inertia P2MW.S_WeierstrassCurve_card_range_galoisRep_three_le_two.ValuationSubring P2MW.S_WeierstrassCurve_card_range_galoisRep_three_le_two.Ideal P2MW.S_WeierstrassCurve_card_range_galoisRep_three_le_two.AlgebraicClosure P2MW.S_WeierstrassCurve_card_range_galoisRep_three_le_two.WeierstrassCurve P2MW.S_WeierstrassCurve_card_range_galoisRep_three_le_two.WeierstrassCurve.Affine P2MW.S_WeierstrassCurve_card_range_galoisRep_three_le_two.WeierstrassCurve.Affine.Point P2MW.S_WeierstrassCurve_card_range_galoisRep_three_le_two.WeierstrassCurve.torsionField"

end
p2m_reactivate "P2MW.S_WeierstrassCurve_card_range_galoisRep_three_le_two.B6Inertia P2MW.S_WeierstrassCurve_card_range_galoisRep_three_le_two.ValuationSubring P2MW.S_WeierstrassCurve_card_range_galoisRep_three_le_two.Ideal P2MW.S_WeierstrassCurve_card_range_galoisRep_three_le_two.AlgebraicClosure P2MW.S_WeierstrassCurve_card_range_galoisRep_three_le_two.WeierstrassCurve P2MW.S_WeierstrassCurve_card_range_galoisRep_three_le_two.WeierstrassCurve.Affine P2MW.S_WeierstrassCurve_card_range_galoisRep_three_le_two.WeierstrassCurve.Affine.Point P2MW.S_WeierstrassCurve_card_range_galoisRep_three_le_two.WeierstrassCurve.torsionField"

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine map mk isIntegral_iff IsIntegral Affine.Point Δ residualGaloisRepOf Affine.Point.galoisRepModuleEnd card apply_eq_self_of_galoisRep_eq_one_of_pow_eq_one"
p2m_open "WeierstrassCurve"

variable (E : WeierstrassCurve ℚ) (p : ℕ)

namespace torsionField

private scoped instance _root_.WeierstrassCurve.torsionField.normal' : Normal ℚ (torsionField E p) := torsionField.normal E p

end torsionField
p2m_export "WeierstrassCurve" "torsionField.normal'"
p2m_reactivate "P2MW.S_WeierstrassCurve_card_range_galoisRep_three_le_two.B6Inertia P2MW.S_WeierstrassCurve_card_range_galoisRep_three_le_two.ValuationSubring P2MW.S_WeierstrassCurve_card_range_galoisRep_three_le_two.Ideal P2MW.S_WeierstrassCurve_card_range_galoisRep_three_le_two.AlgebraicClosure P2MW.S_WeierstrassCurve_card_range_galoisRep_three_le_two.WeierstrassCurve P2MW.S_WeierstrassCurve_card_range_galoisRep_three_le_two.WeierstrassCurve.Affine P2MW.S_WeierstrassCurve_card_range_galoisRep_three_le_two.WeierstrassCurve.Affine.Point P2MW.S_WeierstrassCurve_card_range_galoisRep_three_le_two.WeierstrassCurve.torsionField"
namespace torsionField

private scoped instance _root_.WeierstrassCurve.torsionField.isGalois' : IsGalois ℚ (torsionField E p) := torsionField.isGalois E p

end torsionField
p2m_export "WeierstrassCurve" "torsionField.isGalois'"
p2m_reactivate "P2MW.S_WeierstrassCurve_card_range_galoisRep_three_le_two.B6Inertia P2MW.S_WeierstrassCurve_card_range_galoisRep_three_le_two.ValuationSubring P2MW.S_WeierstrassCurve_card_range_galoisRep_three_le_two.Ideal P2MW.S_WeierstrassCurve_card_range_galoisRep_three_le_two.AlgebraicClosure P2MW.S_WeierstrassCurve_card_range_galoisRep_three_le_two.WeierstrassCurve P2MW.S_WeierstrassCurve_card_range_galoisRep_three_le_two.WeierstrassCurve.Affine P2MW.S_WeierstrassCurve_card_range_galoisRep_three_le_two.WeierstrassCurve.Affine.Point P2MW.S_WeierstrassCurve_card_range_galoisRep_three_le_two.WeierstrassCurve.torsionField"
end WeierstrassCurve
p2m_reactivate "P2MW.S_WeierstrassCurve_card_range_galoisRep_three_le_two.B6Inertia P2MW.S_WeierstrassCurve_card_range_galoisRep_three_le_two.ValuationSubring P2MW.S_WeierstrassCurve_card_range_galoisRep_three_le_two.Ideal P2MW.S_WeierstrassCurve_card_range_galoisRep_three_le_two.AlgebraicClosure P2MW.S_WeierstrassCurve_card_range_galoisRep_three_le_two.WeierstrassCurve P2MW.S_WeierstrassCurve_card_range_galoisRep_three_le_two.WeierstrassCurve.Affine P2MW.S_WeierstrassCurve_card_range_galoisRep_three_le_two.WeierstrassCurve.Affine.Point P2MW.S_WeierstrassCurve_card_range_galoisRep_three_le_two.WeierstrassCurve.torsionField"

section B6R7

p2m_open "WeierstrassCurve P2MW.S_WeierstrassCurve_card_range_galoisRep_three_le_two.WeierstrassCurve WeierstrassCurve.Affine P2MW.S_WeierstrassCurve_card_range_galoisRep_three_le_two.WeierstrassCurve.Affine WeierstrassCurve.Affine.Point P2MW.S_WeierstrassCurve_card_range_galoisRep_three_le_two.WeierstrassCurve.Affine.Point"

local notation "Γ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

def B6R7.MuFixedStatement (W : WeierstrassCurve ℤ) : Prop :=
  ∀ σ : Γ, WeierstrassCurve.Affine.Point.galoisRepModuleEnd (K := AlgebraicClosure ℚ) ℚ
      (W.map (Int.castRingHom ℚ)) 3 σ = 1 →
    ∀ μ : AlgebraicClosure ℚ, μ ^ 3 = 1 → σ μ = μ

theorem B6R7.main (W : WeierstrassCurve ℤ)
    (hcard : Nat.card (Submodule.torsionBy ℤ
      ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point 3) = 3 ^ 2)
    (hμ : B6R7.MuFixedStatement W)
    (hunr : ∀ q : ℕ, q.Prime → q ≠ 3 → ∀ A : ValuationSubring (AlgebraicClosure ℚ),
      A.LiesOverPrime q → ∀ σ ∈ A.inertiaSubgroupIn ℚ,
        WeierstrassCurve.Affine.Point.galoisRepModuleEnd (K := AlgebraicClosure ℚ) ℚ
          (W.map (Int.castRingHom ℚ)) 3 σ = 1)
    (hle2 : ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime 3 →
      Nat.card (WeierstrassCurve.Affine.Point.galoisRepModuleEnd (K := AlgebraicClosure ℚ) ℚ
        (W.map (Int.castRingHom ℚ)) 3 '' (A.inertiaSubgroupIn ℚ : Set Γ)) ≤ 2) :
    Nat.card (Set.range (WeierstrassCurve.Affine.Point.galoisRepModuleEnd
      (K := AlgebraicClosure ℚ) ℚ (W.map (Int.castRingHom ℚ)) 3)) ≤ 2 := by
  have hker := (W.map (Int.castRingHom ℚ)).galoisFactorsThroughFiniteLevel_galoisRepModuleEnd 3 hcard
  haveI := (W.map (Int.castRingHom ℚ)).finiteDimensional_torsionField 3 hcard

  have hunr' : ∀ q : ℕ, q.Prime → q ≠ 3 → ∀ A : ValuationSubring (AlgebraicClosure ℚ),
      A.LiesOverPrime q → (A.inertiaSubgroupIn ℚ).map
        (AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := AlgebraicClosure ℚ)
          ((W.map (Int.castRingHom ℚ)).torsionField 3)) = ⊥ := by
    intro q hq hq3 A hA
    rw [eq_bot_iff]
    rintro _ ⟨σ, hσ, rfl⟩
    rw [Subgroup.mem_bot]
    have hk := ((W.map (Int.castRingHom ℚ)).restrictNormalHom_torsionField_apply_eq_iff 3 hcard hker
      σ 1).mpr (by rw [map_one]; exact hunr q hq hq3 A hA σ hσ)
    rw [map_one] at hk
    exact hk

  have htame' : ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime 3 →
      Nat.card ((A.inertiaSubgroupIn ℚ).map
        (AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := AlgebraicClosure ℚ)
          ((W.map (Int.castRingHom ℚ)).torsionField 3))) ≤ 2 := by
    intro A hA
    have h := (W.map (Int.castRingHom ℚ)).natCard_image_residualGaloisRepOf_eq 3 hcard hker
      (A.inertiaSubgroupIn ℚ)
    have h2 : Nat.card (((W.map (Int.castRingHom ℚ)).residualGaloisRepOf 3 hcard hker).ρ ''
        (A.inertiaSubgroupIn ℚ : Set Γ)) ≤ 2 := hle2 A hA
    rw [h] at h2
    exact h2

  have hζ' : ∃ ζ : (W.map (Int.castRingHom ℚ)).torsionField 3, ζ ^ 2 + ζ + 1 = 0 := by
    haveI : NeZero ((3 : ℕ) : ℚ) := ⟨by norm_num⟩
    obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.prim (M := AlgebraicClosure ℚ) (n := 3)
    have hζL : ζ ∈ (W.map (Int.castRingHom ℚ)).torsionField 3 :=
      (W.map (Int.castRingHom ℚ)).mem_torsionField_of_forall_ker 3 hcard hker ζ
        (fun σ hσ => hμ σ hσ ζ hζ.pow_eq_one)
    refine ⟨⟨ζ, hζL⟩, ?_⟩
    have h1 : ζ ^ 3 = 1 := hζ.pow_eq_one
    have hne : ζ ≠ 1 := hζ.ne_one (by norm_num)
    have h2 : (ζ - 1) * (ζ ^ 2 + ζ + 1) = 0 := by ring_nf; rw [h1]; ring
    have h3 : ζ ^ 2 + ζ + 1 = 0 := (mul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr hne)
    apply Subtype.val_injective
    simpa using h3

  have hfin := B6P3.finrank_le_two_of_inertia_le ((W.map (Int.castRingHom ℚ)).torsionField 3)
    hunr' htame' hζ'
  have hrange := (W.map (Int.castRingHom ℚ)).natCard_range_residualGaloisRepOf_eq_finrank 3 hcard hker

  exact hrange ▸ hfin

end B6R7
p2m_reactivate "P2MW.S_WeierstrassCurve_card_range_galoisRep_three_le_two.B6Inertia P2MW.S_WeierstrassCurve_card_range_galoisRep_three_le_two.ValuationSubring P2MW.S_WeierstrassCurve_card_range_galoisRep_three_le_two.Ideal P2MW.S_WeierstrassCurve_card_range_galoisRep_three_le_two.AlgebraicClosure P2MW.S_WeierstrassCurve_card_range_galoisRep_three_le_two.WeierstrassCurve P2MW.S_WeierstrassCurve_card_range_galoisRep_three_le_two.WeierstrassCurve.Affine P2MW.S_WeierstrassCurve_card_range_galoisRep_three_le_two.WeierstrassCurve.Affine.Point P2MW.S_WeierstrassCurve_card_range_galoisRep_three_le_two.WeierstrassCurve.torsionField"

open _root_.WeierstrassCurve _root_.P2MW.S_WeierstrassCurve_card_range_galoisRep_three_le_two.WeierstrassCurve _root_.WeierstrassCurve.Affine _root_.P2MW.S_WeierstrassCurve_card_range_galoisRep_three_le_two.WeierstrassCurve.Affine _root_.WeierstrassCurve.Affine.Point _root_.P2MW.S_WeierstrassCurve_card_range_galoisRep_three_le_two.WeierstrassCurve.Affine.Point in

theorem solution (W : WeierstrassCurve ℤ) (hΔ : W.Δ ≠ 0)
    (hcard : Nat.card (Submodule.torsionBy ℤ
      ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point 3) = 3 ^ 2)
    (hunr : ∀ q : ℕ, q.Prime → q ≠ 3 → ∀ A : ValuationSubring (AlgebraicClosure ℚ),
      A.LiesOverPrime q → ∀ σ ∈ A.inertiaSubgroupIn ℚ,
        WeierstrassCurve.Affine.Point.galoisRepModuleEnd (K := AlgebraicClosure ℚ) ℚ
          (W.map (Int.castRingHom ℚ)) 3 σ = 1)
    (hle2 : ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime 3 →
      Nat.card (WeierstrassCurve.Affine.Point.galoisRepModuleEnd (K := AlgebraicClosure ℚ) ℚ
        (W.map (Int.castRingHom ℚ)) 3 ''
          (A.inertiaSubgroupIn ℚ : Set (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))) ≤ 2) :
    Nat.card (Set.range (WeierstrassCurve.Affine.Point.galoisRepModuleEnd
      (K := AlgebraicClosure ℚ) ℚ (W.map (Int.castRingHom ℚ)) 3)) ≤ 2 :=
  B6R7.main W hcard
    (fun σ hσ μ hμ =>
      WeierstrassCurve.apply_eq_self_of_galoisRep_eq_one_of_pow_eq_one W 3 hΔ σ hσ μ hμ)
    hunr hle2

#print axioms solution

end S_WeierstrassCurve_card_range_galoisRep_three_le_two
end P2MW
export P2MW.S_WeierstrassCurve_card_range_galoisRep_three_le_two (solution)
