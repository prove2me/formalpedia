-- Prove2me | solution 1 for ValuationSubring.exists_mem_inertiaSubgroupIn_forall_apply_algebraMap_eq_of_isCyclotomicExtension
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/bfc39e1a-3721-5112-9ede-b1ad37ef9996

import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import Theorems.Thm_ValuationSubring_exists_mem_inertiaSubgroupIn_restrictNormal_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_exists_mem_inertiaSubgroupIn_forall_apply_algebraMap_eq_of_isCyclotomicExtension

set_option autoImplicit false

open scoped Pointwise NumberField

namespace KummerUnram

section Transport
variable {K K' : Type*} [Field K] [Field K']

theorem mem_nonunits_comap_iff (A : ValuationSubring K') (φ : K →+* K') (x : K) :
    x ∈ (A.comap φ).nonunits ↔ φ x ∈ A.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_nonunits_iff_or, map_eq_zero_iff φ φ.injective,
    ← map_inv₀, ValuationSubring.mem_comap]

theorem inv_mem_of_not_mem_nonunits (A : ValuationSubring K) {x : K} (h : x ∉ A.nonunits) : x⁻¹ ∈ A := by
  rw [ValuationSubring.mem_nonunits_iff_or, not_or, not_not] at h
  exact h.2

theorem ne_top_of_mem_nonunits (A : ValuationSubring K) {x : K} (hx : x ∈ A.nonunits) (hx0 : x ≠ 0) : A ≠ ⊤ := by
  intro h
  rw [ValuationSubring.mem_nonunits_iff_or] at hx
  rcases hx with hx | hx
  · exact hx0 hx
  · apply hx; rw [h]; trivial

theorem mem_nonunits_of_mem_of_not_isUnit (A : ValuationSubring K) {x : K} (hx : x ∈ A) (h : ¬ IsUnit (⟨x, hx⟩ : A)) :
    x ∈ A.nonunits :=
  ValuationSubring.coe_mem_nonunits_iff.mpr h

theorem nonunits_mul_mem (A : ValuationSubring K) {x y : K} (hx : x ∈ A.nonunits) (hy : y ∈ A) : x * y ∈ A.nonunits := by
  have hxA : x ∈ A := A.nonunits_le hx
  have h1 : (⟨x, hxA⟩ : A) ∈ IsLocalRing.maximalIdeal A := ValuationSubring.coe_mem_nonunits_iff.mp hx
  have h2 := Ideal.mul_mem_right (⟨y, hy⟩ : A) _ h1
  exact ValuationSubring.coe_mem_nonunits_iff.mpr h2

theorem not_mem_nonunits_of_inv_mem (A : ValuationSubring K) {x : K} (hx0 : x ≠ 0) (hxi : x⁻¹ ∈ A) : x ∉ A.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff_or, not_or, not_not]
  exact ⟨hx0, hxi⟩

theorem valuation_eq_one_of_mem_of_not_mem_nonunits (A : ValuationSubring K) {x : K} (hx : x ∈ A) (hxn : x ∉ A.nonunits) :
    A.valuation x = 1 :=
  le_antisymm ((A.valuation_le_one_iff x).mpr hx) (not_lt.mp (fun h => hxn (A.mem_nonunits_iff.mpr h)))

end Transport
end KummerUnram

namespace InertiaSurj

open IsCyclotomicExtension NumberField

section Cyclotomic

variable {p : ℕ} [hp : Fact p.Prime] {M : Type*} [Field M] [CharZero M] [IsCyclotomicExtension {p} ℚ M]

theorem exists_sub_eq_mul (τ : M ≃ₐ[ℚ] M) (y : M) (hy : y ∈ Algebra.adjoin ℤ ({zeta p ℚ M} : Set M)) :
    ∃ c ∈ Algebra.adjoin ℤ ({zeta p ℚ M} : Set M), τ y - y = (zeta p ℚ M - 1) * c := by
  set ζ := zeta p ℚ M with hζdef
  have hζ : IsPrimitiveRoot ζ p := zeta_spec p ℚ M

  have hτζ : ∃ m : ℕ, τ ζ = ζ ^ m := by
    have h1 : (τ ζ) ^ p = 1 := by rw [← map_pow, hζ.pow_eq_one, map_one]
    obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_pow_eq_one h1
    exact ⟨i, hi.symm⟩
  obtain ⟨m, hm⟩ := hτζ

  have hτS : ∀ z ∈ Algebra.adjoin ℤ ({ζ} : Set M), τ z ∈ Algebra.adjoin ℤ ({ζ} : Set M) := by
    intro z hz
    have : (τ : M →+* M).toIntAlgHom z ∈ (Algebra.adjoin ℤ ({ζ} : Set M)).map (τ : M →+* M).toIntAlgHom := ⟨z, hz, rfl⟩
    rw [AlgHom.map_adjoin, Set.image_singleton] at this
    have hle : Algebra.adjoin ℤ {(τ : M →+* M).toIntAlgHom ζ} ≤ Algebra.adjoin ℤ ({ζ} : Set M) := by
      rw [Algebra.adjoin_le_iff, Set.singleton_subset_iff]
      show τ ζ ∈ Algebra.adjoin ℤ ({ζ} : Set M)
      rw [hm]; exact Subalgebra.pow_mem _ (Algebra.self_mem_adjoin_singleton ℤ ζ) _
    exact hle this
  induction hy using Algebra.adjoin_induction with
  | mem x hx =>
      rw [Set.mem_singleton_iff] at hx
      subst hx

      rcases Nat.eq_zero_or_pos m with h0 | hpos
      · exfalso
        rw [h0, pow_zero] at hm
        have : ζ = 1 := τ.injective (by rw [hm, map_one])
        exact hζ.ne_one hp.out.one_lt this
      · refine ⟨ζ * (Finset.range (m - 1)).sum (fun i => ζ ^ i), ?_, ?_⟩
        · exact Subalgebra.mul_mem _ (Algebra.self_mem_adjoin_singleton ℤ ζ)
            (Subalgebra.sum_mem _ fun i _ => Subalgebra.pow_mem _ (Algebra.self_mem_adjoin_singleton ℤ ζ) _)
        · rw [hm]
          have h := geom_sum_mul ζ (m - 1)
          calc ζ ^ m - ζ = ζ * (ζ ^ (m - 1) - 1) := by
                  rw [mul_sub, mul_one, ← pow_succ', Nat.sub_add_cancel hpos]
            _ = (ζ - 1) * (ζ * (Finset.range (m - 1)).sum (fun i => ζ ^ i)) := by rw [← h]; ring
  | algebraMap r => exact ⟨0, Subalgebra.zero_mem _, by simp⟩
  | add x y hx hy ihx ihy =>
      obtain ⟨c, hc, hcx⟩ := ihx
      obtain ⟨d, hd, hdy⟩ := ihy
      exact ⟨c + d, Subalgebra.add_mem _ hc hd, by rw [map_add, mul_add, ← hcx, ← hdy]; ring⟩
  | mul x y hx hy ihx ihy =>
      obtain ⟨c, hc, hcx⟩ := ihx
      obtain ⟨d, hd, hdy⟩ := ihy
      refine ⟨τ x * d + c * y, Subalgebra.add_mem _ (Subalgebra.mul_mem _ (hτS x hx) hd) (Subalgebra.mul_mem _ hc hy), ?_⟩
      have : τ (x * y) - x * y = τ x * (τ y - y) + (τ x - x) * y := by rw [map_mul]; ring
      rw [this, hcx, hdy]; ring

theorem exists_sub_eq_mul_of_isIntegral (τ : M ≃ₐ[ℚ] M) (a : M) (ha : IsIntegral ℤ a) :
    ∃ c : M, IsIntegral ℤ c ∧ τ a - a = (zeta p ℚ M - 1) * c := by
  haveI := Rat.isIntegralClosure_adjoin_singleton_of_prime (K := M) (zeta_spec p ℚ M)
  have hmem : a ∈ Algebra.adjoin ℤ ({zeta p ℚ M} : Set M) := by
    obtain ⟨y, hy⟩ := (IsIntegralClosure.isIntegral_iff (A := Algebra.adjoin ℤ ({zeta p ℚ M} : Set M))).mp ha
    rw [← hy]; exact y.2
  obtain ⟨c, hc, h⟩ := exists_sub_eq_mul τ a hmem
  refine ⟨c, ?_, h⟩
  exact (IsIntegralClosure.isIntegral_iff (A := Algebra.adjoin ℤ ({zeta p ℚ M} : Set M)) (R := ℤ) (B := M)).mpr ⟨⟨c, hc⟩, rfl⟩

end Cyclotomic

end InertiaSurj

namespace InertiaSurj

open IsCyclotomicExtension NumberField

section Val

variable {p : ℕ} [hp : Fact p.Prime] {M : Type*} [Field M] [CharZero M] [IsCyclotomicExtension {p} ℚ M] [NumberField M]

theorem mem_of_isIntegral (B : ValuationSubring M) {a : M} (ha : IsIntegral ℤ a) : a ∈ B := by
  have h : IsIntegral B a := ha.tower_top
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp h
  rw [← hy]; exact y.2

noncomputable def toB (B : ValuationSubring M) : 𝓞 M →+* B :=
  ((algebraMap (𝓞 M) M)).codRestrict B.toSubring (fun a => mem_of_isIntegral B a.isIntegral_coe)

@[scoped simp] theorem coe_toB (B : ValuationSubring M) (a : 𝓞 M) : ((toB B a : B) : M) = (a : M) := rfl

variable (B : ValuationSubring M) (hB : (p : M) ∈ B.nonunits)
include hB

theorem comap_maximalIdeal_eq :
    (IsLocalRing.maximalIdeal B).comap (toB B) = Ideal.span {(zeta_spec p ℚ M).toInteger - 1} := by
  set P := (IsLocalRing.maximalIdeal B).comap (toB B) with hP
  haveI hPp : P.IsPrime := Ideal.comap_isPrime _ _
  haveI : P.LiesOver (Ideal.span {(p : ℤ)}) := by
    have hpP : (p : ℤ) ∈ P.under ℤ := by
      rw [Ideal.under_def, Ideal.mem_comap, hP, Ideal.mem_comap]
      apply ValuationSubring.coe_mem_nonunits_iff.mp
      simpa using hB
    haveI : (P.under ℤ).IsPrime := Ideal.IsPrime.under ℤ P
    have hprime : (Ideal.span {(p : ℤ)}).IsPrime :=
      (Ideal.span_singleton_prime (by exact_mod_cast hp.out.ne_zero)).mpr (Nat.prime_iff_prime_int.mp hp.out)
    have hmax : (Ideal.span {(p : ℤ)}).IsMaximal := hprime.isMaximal (by simp [hp.out.ne_zero])
    exact ⟨hmax.eq_of_le (Ideal.IsPrime.ne_top inferInstance) ((Ideal.span_singleton_le_iff_mem _).mpr hpP)⟩
  exact Rat.eq_span_zeta_sub_one_of_liesOver' p M (zeta_spec p ℚ M) P

theorem not_mem_nonunits_iff (a : 𝓞 M) :
    (a : M) ∉ B.nonunits ↔ a ∉ Ideal.span {(zeta_spec p ℚ M).toInteger - 1} := by
  rw [← comap_maximalIdeal_eq B hB, Ideal.mem_comap, not_iff_not]
  show ((toB B a : B) : M) ∈ B.nonunits ↔ _
  exact ValuationSubring.coe_mem_nonunits_iff

theorem zeta_sub_one_mem_nonunits : zeta p ℚ M - 1 ∈ B.nonunits := by
  have h : (zeta_spec p ℚ M).toInteger - 1 ∈ (IsLocalRing.maximalIdeal B).comap (toB B) := by
    rw [comap_maximalIdeal_eq B hB]; exact Ideal.subset_span rfl
  rw [Ideal.mem_comap] at h
  have := ValuationSubring.coe_mem_nonunits_iff.mpr h
  simpa using this

theorem sub_mem_nonunits (τ : M ≃ₐ[ℚ] M) (a : M) (ha : IsIntegral ℤ a) : τ a - a ∈ B.nonunits := by
  obtain ⟨c, hc, h⟩ := exists_sub_eq_mul_of_isIntegral (p := p) τ a ha
  rw [h]
  exact KummerUnram.nonunits_mul_mem B (zeta_sub_one_mem_nonunits B hB) (mem_of_isIntegral B hc)

theorem map_not_mem_nonunits (τ : M ≃ₐ[ℚ] M) (a : M) (ha : IsIntegral ℤ a) (hna : a ∉ B.nonunits) : τ a ∉ B.nonunits := by
  intro h
  apply hna
  have : a = τ a - (τ a - a) := by ring
  rw [this]
  exact B.nonunits.sub_mem h (sub_mem_nonunits B hB τ a ha)

theorem exists_eq_div (x : M) (hx : x ∈ B) :
    ∃ a s : 𝓞 M, (s : M) ∉ B.nonunits ∧ x = (a : M) * ((s : M))⁻¹ := by
  classical
  set 𝔭 : Ideal (𝓞 M) := Ideal.span {(zeta_spec p ℚ M).toInteger - 1} with h𝔭
  haveI : 𝔭.IsPrime := by rw [h𝔭]; exact Rat.isPrime_span_zeta_sub_one' (hζ := zeta_spec p ℚ M)
  have h𝔭ne : 𝔭 ≠ ⊥ := by
    rw [h𝔭, Ne, Ideal.span_singleton_eq_bot, sub_eq_zero]
    intro h
    apply (zeta_spec p ℚ M).ne_one hp.out.one_lt
    have := congrArg (fun x : 𝓞 M => (x : M)) h
    simpa using this
  let w : IsDedekindDomain.HeightOneSpectrum (𝓞 M) := ⟨𝔭, inferInstance, h𝔭ne⟩
  have hp0 : (p : M) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hBtop : B ≠ ⊤ := KummerUnram.ne_top_of_mem_nonunits B hB hp0
  have hle : IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime M w ≤ B := by
    rintro y ⟨a, s, hs, rfl⟩
    have hsn : ((s : 𝓞 M) : M) ∉ B.nonunits := (not_mem_nonunits_iff B hB s).mpr hs
    exact B.mul_mem _ _ (mem_of_isIntegral B a.isIntegral_coe) (KummerUnram.inv_mem_of_not_mem_nonunits B hsn)
  have hVB : IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime M w = B :=
    ValuationSubring.eq_of_le_of_ne_top _ hle hBtop
  have hx' : x ∈ IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime M w := by rw [hVB]; exact hx
  obtain ⟨a, s, hs, rfl⟩ := hx'
  exact ⟨a, s, (not_mem_nonunits_iff B hB s).mpr hs, rfl⟩

end Val

end InertiaSurj
p2m_reactivate "P2MW.S_ValuationSubring_exists_mem_inertiaSubgroupIn_forall_apply_algebraMap_eq_of_isCyclotomicExtension.InertiaSurj"

namespace InertiaSurj

open IsCyclotomicExtension NumberField

section Inertia

variable {p : ℕ} [hp : Fact p.Prime] {M : Type*} [Field M] [CharZero M] [IsCyclotomicExtension {p} ℚ M] [NumberField M]
variable (B : ValuationSubring M) (hB : (p : M) ∈ B.nonunits)
include hB

theorem map_mem (τ : M ≃ₐ[ℚ] M) (x : M) (hx : x ∈ B) : τ x ∈ B := by
  obtain ⟨a, s, hs, rfl⟩ := exists_eq_div B hB x hx
  rw [map_mul, map_inv₀]
  have hτa : IsIntegral ℤ (τ (a : M)) := a.isIntegral_coe.map τ
  have hτs : τ (s : M) ∉ B.nonunits := map_not_mem_nonunits B hB τ s s.isIntegral_coe hs
  exact B.mul_mem _ _ (mem_of_isIntegral B hτa) (KummerUnram.inv_mem_of_not_mem_nonunits B hτs)

theorem smul_eq (τ : M ≃ₐ[ℚ] M) : τ • B = B := by
  apply le_antisymm
  · intro x hx
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem] at hx
    have := map_mem B hB τ _ hx
    simpa using this
  · intro x hx
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
    exact map_mem B hB τ⁻¹ x hx

theorem smul_sub_mem_nonunits (τ : M ≃ₐ[ℚ] M) (x : M) (hx : x ∈ B) : τ x - x ∈ B.nonunits := by
  obtain ⟨a, s, hs, rfl⟩ := exists_eq_div B hB x hx
  have hs0 : (s : M) ≠ 0 := fun h => hs (by rw [h]; exact B.nonunits.zero_mem)
  have hτs : τ (s : M) ∉ B.nonunits := map_not_mem_nonunits B hB τ s s.isIntegral_coe hs
  have hτs0 : τ (s : M) ≠ 0 := fun h => hτs (by rw [h]; exact B.nonunits.zero_mem)

  have key : τ ((a : M) * ((s : M))⁻¹) - (a : M) * ((s : M))⁻¹ =
      (τ (a : M) - a) * (τ (s : M))⁻¹ - ((a : M) * ((s : M))⁻¹) * ((τ (s : M) - s) * (τ (s : M))⁻¹) := by
    rw [map_mul, map_inv₀]
    field_simp
    ring
  rw [key]
  apply B.nonunits.sub_mem
  · exact KummerUnram.nonunits_mul_mem B (sub_mem_nonunits B hB τ a a.isIntegral_coe)
      (KummerUnram.inv_mem_of_not_mem_nonunits B hτs)
  · have h1 : (τ (s : M) - s) * (τ (s : M))⁻¹ ∈ B.nonunits :=
      KummerUnram.nonunits_mul_mem B (sub_mem_nonunits B hB τ s s.isIntegral_coe)
        (KummerUnram.inv_mem_of_not_mem_nonunits B hτs)
    rw [mul_comm]
    exact KummerUnram.nonunits_mul_mem B h1 hx

theorem mem_inertiaSubgroupIn (τ : M ≃ₐ[ℚ] M) : τ ∈ B.inertiaSubgroupIn ℚ := by
  have hdec : τ ∈ B.decompositionSubgroup ℚ := smul_eq B hB τ
  refine Subgroup.mem_map.mpr ⟨⟨τ, hdec⟩, ?_, rfl⟩
  rw [ValuationSubring.inertiaSubgroup, MonoidHom.mem_ker]
  ext r
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective r
  rw [MulSemiringAction.toRingAut_apply, MulSemiringAction.toRingEquiv_apply, RingAut.one_apply, ← IsLocalRing.ResidueField.residue_smul]
  show IsLocalRing.residue B ((⟨τ, hdec⟩ : B.decompositionSubgroup ℚ) • x) = IsLocalRing.residue B x
  rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  have hmem : (((⟨τ, hdec⟩ : B.decompositionSubgroup ℚ) • x - x : B) : M) ∈ B.nonunits := by
    have : (((⟨τ, hdec⟩ : B.decompositionSubgroup ℚ) • x - x : B) : M) = τ (x : M) - x := rfl
    rw [this]
    exact smul_sub_mem_nonunits B hB τ x x.2
  exact (ValuationSubring.coe_mem_nonunits_iff.mp hmem |> (IsLocalRing.mem_maximalIdeal _).mp) hu

end Inertia
p2m_reactivate "P2MW.S_ValuationSubring_exists_mem_inertiaSubgroupIn_forall_apply_algebraMap_eq_of_isCyclotomicExtension.InertiaSurj"

end InertiaSurj
p2m_reactivate "P2MW.S_ValuationSubring_exists_mem_inertiaSubgroupIn_forall_apply_algebraMap_eq_of_isCyclotomicExtension.InertiaSurj"

theorem InertiaSurj.isGalois_rat_algebraicClosure [alg : Algebra ℚ (AlgebraicClosure ℚ)] : IsGalois ℚ (AlgebraicClosure ℚ) := by
  have h : alg = AlgebraicClosure.instAlgebra ℚ := Subsingleton.elim _ _
  subst h
  haveI halg : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
  haveI : Normal ℚ (AlgebraicClosure ℚ) :=
    { toIsAlgebraic := halg
      splits' := fun x => IsAlgClosed.splits _ }
  haveI : Algebra.IsSeparable ℚ (AlgebraicClosure ℚ) := Algebra.IsAlgebraic.isSeparable_of_perfectField
  exact isGalois_iff.mpr ⟨inferInstance, inferInstance⟩

theorem solution
    (p : ℕ) [Fact p.Prime] (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    [Algebra L (AlgebraicClosure ℚ)]
    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    (s : L ≃ₐ[ℚ] L) :
    ∃ σ' ∈ Pl.inertiaSubgroupIn ℚ, ∀ l : L, σ' (algebraMap L (AlgebraicClosure ℚ) l) = algebraMap L (AlgebraicClosure ℚ) (s l) := by
  classical

  let ι : L →ₐ[ℚ] AlgebraicClosure ℚ := (algebraMap L (AlgebraicClosure ℚ)).toRatAlgHom
  have hι : ∀ l : L, ι l = algebraMap L (AlgebraicClosure ℚ) l := fun _ => rfl
  let Mf : IntermediateField ℚ (AlgebraicClosure ℚ) := ι.fieldRange
  let e : L ≃ₐ[ℚ] ↥Mf := AlgEquiv.ofInjectiveField ι
  have he : ∀ l : L, ((e l : ↥Mf) : AlgebraicClosure ℚ) = algebraMap L (AlgebraicClosure ℚ) l := fun _ => rfl
  haveI : IsCyclotomicExtension {p} ℚ ↥Mf := IsCyclotomicExtension.equiv {p} ℚ L e
  haveI : NumberField ↥Mf := IsCyclotomicExtension.numberField {p} ℚ ↥Mf
  haveI : IsGalois ℚ ↥Mf := IsCyclotomicExtension.isGalois {p} ℚ ↥Mf

  let B : ValuationSubring ↥Mf := Pl.comap (algebraMap ↥Mf (AlgebraicClosure ℚ))
  have hB : ((p : ℕ) : ↥Mf) ∈ B.nonunits := by
    rw [KummerUnram.mem_nonunits_comap_iff, map_natCast]
    exact hPl

  let τ : ↥Mf ≃ₐ[ℚ] ↥Mf := e.symm.trans (s.trans e)
  have hτ : τ ∈ B.inertiaSubgroupIn ℚ := InertiaSurj.mem_inertiaSubgroupIn B hB τ

  haveI hGal : IsGalois ℚ (AlgebraicClosure ℚ) := InertiaSurj.isGalois_rat_algebraicClosure
  haveI hNorm : Normal ℚ ↥Mf := IsGalois.to_normal
  obtain ⟨σ, hσ, hστ⟩ :=
    @ValuationSubring.exists_mem_inertiaSubgroupIn_restrictNormal_eq ℚ (AlgebraicClosure ℚ) _ _ _ hGal Mf hNorm Pl τ hτ
  refine ⟨σ, hσ, fun l => ?_⟩
  have h3 : ∀ y : ↥Mf, σ (y : AlgebraicClosure ℚ) = ((τ y : ↥Mf) : AlgebraicClosure ℚ) := by
    intro y
    rw [← hστ]
    exact (AlgEquiv.restrictNormal_commutes σ ↥Mf y).symm
  rw [← he l, h3, ← he (s l)]
  congr 1
  show (e.symm.trans (s.trans e)) (e l) = e (s l)
  simp

end S_ValuationSubring_exists_mem_inertiaSubgroupIn_forall_apply_algebraMap_eq_of_isCyclotomicExtension
end P2MW
export P2MW.S_ValuationSubring_exists_mem_inertiaSubgroupIn_forall_apply_algebraMap_eq_of_isCyclotomicExtension (solution)
