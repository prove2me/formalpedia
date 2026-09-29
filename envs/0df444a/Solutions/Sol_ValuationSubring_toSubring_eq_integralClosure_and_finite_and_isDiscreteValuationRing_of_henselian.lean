-- Prove2me | solution 1 for ValuationSubring.toSubring_eq_integralClosure_and_finite_and_isDiscreteValuationRing_of_henselian
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/f6c7f25b-83b3-5c6c-8b1b-db9106e61af0

import Mathlib
import Theorems.Thm_HenselianLocalRing_existsUnique_isIdempotentElem_mk_eq_of_moduleFinite
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_toSubring_eq_integralClosure_and_finite_and_isDiscreteValuationRing_of_henselian

set_option autoImplicit false

set_option maxHeartbeats 1600000

universe u v

namespace S17Hens

theorem isArtinianRing_quotient_map_maximalIdeal
    {R : Type u} [CommRing R] [IsLocalRing R]
    {S : Type v} [CommRing S] [Algebra R S] [Module.Finite R S] :
    IsArtinianRing (S ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R S)) := by
  set J : Ideal S := (IsLocalRing.maximalIdeal R).map (algebraMap R S) with hJ
  let k := R ⧸ IsLocalRing.maximalIdeal R
  letI : Field k := Ideal.Quotient.field _
  have hJR : ∀ r ∈ IsLocalRing.maximalIdeal R, algebraMap R (S ⧸ J) r = 0 := by
    intro r hr
    rw [IsScalarTower.algebraMap_apply R S (S ⧸ J), Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_map_of_mem _ hr
  letI : Algebra k (S ⧸ J) := (Ideal.Quotient.lift _ (algebraMap R (S ⧸ J)) hJR).toAlgebra
  haveI : IsScalarTower R k (S ⧸ J) := IsScalarTower.of_algebraMap_eq (fun r => rfl)
  haveI : Module.Finite k (S ⧸ J) := Module.Finite.of_restrictScalars_finite R k (S ⧸ J)
  exact IsArtinianRing.of_finite k (S ⧸ J)

theorem isLocalRing_of_isDomain_of_moduleFinite
    {R : Type u} [CommRing R] [HenselianLocalRing R]
    {S : Type v} [CommRing S] [IsDomain S] [Algebra R S] [Module.Finite R S] : IsLocalRing S := by
  classical
  by_contra hS

  have h1 : ∃ a : S, ¬ IsUnit a ∧ ¬ IsUnit (1 - a) := by
    by_contra h
    push Not at h
    exact hS (IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => by
      by_cases ha : IsUnit a
      · exact Or.inl ha
      · exact Or.inr (h a ha))
  obtain ⟨a, ha, ha'⟩ := h1
  obtain ⟨m₁, hm₁, ham₁⟩ := exists_max_ideal_of_mem_nonunits ha
  obtain ⟨m₂, hm₂, ham₂⟩ := exists_max_ideal_of_mem_nonunits ha'
  have hne : m₁ ≠ m₂ := by
    intro h
    subst h
    have : (1 : S) ∈ m₁ := by
      have := m₁.add_mem ham₁ ham₂
      rwa [add_sub_cancel] at this
    exact hm₁.ne_top ((Ideal.eq_top_iff_one _).mpr this)

  set J : Ideal S := (IsLocalRing.maximalIdeal R).map (algebraMap R S) with hJ
  have hJle : ∀ m : Ideal S, m.IsMaximal → J ≤ m := by
    intro m hm
    rw [hJ, Ideal.map_le_iff_le_comap]
    haveI := hm
    have hmax : (m.comap (algebraMap R S)).IsMaximal := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal m
    rw [IsLocalRing.eq_maximalIdeal hmax]

  haveI : IsArtinianRing (S ⧸ J) := isArtinianRing_quotient_map_maximalIdeal
  have hsurj : Function.Surjective (Ideal.Quotient.mk J) := Ideal.Quotient.mk_surjective
  have hmaxq : ∀ m : Ideal S, m.IsMaximal → (m.map (Ideal.Quotient.mk J)).IsMaximal := by
    intro m hm
    rcases Ideal.map_eq_top_or_isMaximal_of_surjective _ hsurj hm with h | h
    · exfalso
      have : m = ⊤ := by
        have h2 := congrArg (Ideal.comap (Ideal.Quotient.mk J)) h
        rw [Ideal.comap_map_of_surjective _ hsurj, Ideal.comap_top] at h2
        have hker : Ideal.comap (Ideal.Quotient.mk J) ⊥ = J := by
          rw [← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
        rw [hker, sup_eq_left.mpr (hJle m hm)] at h2
        exact h2
      exact hm.ne_top this
    · exact h
  let M₁ : MaximalSpectrum (S ⧸ J) := ⟨m₁.map (Ideal.Quotient.mk J), hmaxq m₁ hm₁⟩
  let M₂ : MaximalSpectrum (S ⧸ J) := ⟨m₂.map (Ideal.Quotient.mk J), hmaxq m₂ hm₂⟩
  have hM : M₁ ≠ M₂ := by
    intro h
    apply hne
    have h2 : m₁.map (Ideal.Quotient.mk J) = m₂.map (Ideal.Quotient.mk J) := congrArg MaximalSpectrum.asIdeal h
    have h3 := congrArg (Ideal.comap (Ideal.Quotient.mk J)) h2
    rw [Ideal.comap_map_of_surjective _ hsurj, Ideal.comap_map_of_surjective _ hsurj] at h3
    have hker : Ideal.comap (Ideal.Quotient.mk J) ⊥ = J := by
      rw [← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
    rwa [hker, sup_eq_left.mpr (hJle m₁ hm₁), sup_eq_left.mpr (hJle m₂ hm₂)] at h3

  let π := IsArtinianRing.quotNilradicalEquivPi (S ⧸ J)
  let f₀ : ∀ I : MaximalSpectrum (S ⧸ J), (S ⧸ J) ⧸ I.asIdeal := Pi.single M₁ 1
  have hf₀ : IsIdempotentElem f₀ := by
    show f₀ * f₀ = f₀
    ext I
    by_cases hI : I = M₁
    · subst hI; simp [f₀]
    · simp [f₀, hI]
  have hf₀0 : f₀ ≠ 0 := by
    intro h
    have := congrFun h M₁
    simp [f₀] at this
    exact M₁.isMaximal.ne_top (Ideal.Quotient.zero_eq_one_iff.mp this.symm)
  have hf₀1 : f₀ ≠ 1 := by
    intro h
    have := congrFun h M₂
    have h0 : f₀ M₂ = 0 := Pi.single_eq_of_ne hM.symm _
    rw [h0, Pi.one_apply] at this
    exact M₂.isMaximal.ne_top (Ideal.Quotient.zero_eq_one_iff.mp this)
  let ē₀ := π.symm f₀
  have hē₀ : IsIdempotentElem ē₀ := by
    show π.symm f₀ * π.symm f₀ = π.symm f₀
    rw [← map_mul, hf₀.eq]

  have hnil : ∀ y ∈ RingHom.ker (Ideal.Quotient.mk (nilradical (S ⧸ J))), IsNilpotent y := by
    intro y hy
    rw [Ideal.mk_ker] at hy
    exact hy
  obtain ⟨ē, hē, hēē₀⟩ := exists_isIdempotentElem_eq_of_ker_isNilpotent (Ideal.Quotient.mk (nilradical (S ⧸ J))) hnil ē₀
    (Ideal.Quotient.mk_surjective ē₀) hē₀

  obtain ⟨e, ⟨he, hemk⟩, -⟩ := HenselianLocalRing.existsUnique_isIdempotentElem_mk_eq_of_moduleFinite ē hē

  rcases IsIdempotentElem.iff_eq_zero_or_one.mp he with h0 | h1
  · apply hf₀0
    have : ē = 0 := by rw [← hemk, h0, map_zero]
    have : ē₀ = 0 := by rw [← hēē₀, this, map_zero]
    have : f₀ = π 0 := by rw [← this]; exact (π.apply_symm_apply f₀).symm
    rw [this, map_zero]
  · apply hf₀1
    have : ē = 1 := by rw [← hemk, h1, map_one]
    have : ē₀ = 1 := by rw [← hēē₀, this, map_one]
    have : f₀ = π 1 := by rw [← this]; exact (π.apply_symm_apply f₀).symm
    rw [this, map_one]

end S17Hens

namespace S17Hens

open Polynomial in

theorem mem_of_isIntegral {K F : Type} [Field K] [Field F] [Algebra K F]
    (O : ValuationSubring K) [Algebra O F] [IsScalarTower O K F]
    (O' : ValuationSubring F) (hO' : ∀ x : K, algebraMap K F x ∈ O' ↔ x ∈ O)
    {y : F} (hy : IsIntegral O y) : y ∈ O' := by
  by_contra hyO
  obtain ⟨p, hp, hpy⟩ := hy

  have hy0 : y ≠ 0 := fun h => hyO (h ▸ O'.zero_mem)
  have hyinv : O'.valuation y⁻¹ < 1 := by
    rw [map_inv₀, inv_lt_one₀ ((Valuation.pos_iff _).mpr hy0)]
    exact lt_of_not_ge fun h => hyO ((O'.valuation_le_one_iff y).mp h)
  have hcoef : ∀ i, O'.valuation (algebraMap O F (p.coeff i)) ≤ 1 := by
    intro i
    rw [O'.valuation_le_one_iff, IsScalarTower.algebraMap_apply O K F]
    exact (hO' _).mpr (p.coeff i).2

  set n := p.natDegree with hn
  have heval : y ^ n + ∑ i ∈ Finset.range n, algebraMap O F (p.coeff i) * y ^ i = 0 := by
    have h := hpy
    rw [eval₂_eq_sum_range, Finset.sum_range_succ, hp.coeff_natDegree, map_one, one_mul, add_comm] at h
    exact h
  have hone : (1 : F) = - ∑ i ∈ Finset.range n, algebraMap O F (p.coeff i) * (y⁻¹) ^ (n - i) := by
    have hyn : y ^ n ≠ 0 := pow_ne_zero _ hy0
    have h2 := congrArg (fun z => z * (y⁻¹) ^ n) heval
    simp only [add_mul, zero_mul, Finset.sum_mul] at h2
    rw [← mul_pow, mul_inv_cancel₀ hy0, one_pow] at h2
    rw [eq_neg_iff_add_eq_zero, ← h2]
    congr 1
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [Finset.mem_range] at hi
    rw [mul_assoc]
    congr 1
    rw [inv_pow, inv_pow, ← div_eq_mul_inv, eq_div_iff hyn, inv_mul_eq_iff_eq_mul₀ (pow_ne_zero _ hy0), ← pow_add,
      Nat.sub_add_cancel hi.le]
  have hlt : O'.valuation (∑ i ∈ Finset.range n, algebraMap O F (p.coeff i) * (y⁻¹) ^ (n - i)) < 1 := by
    apply Valuation.map_sum_lt _ one_ne_zero
    intro i hi
    rw [Finset.mem_range] at hi
    rw [map_mul, map_pow]
    calc O'.valuation (algebraMap O F (p.coeff i)) * O'.valuation y⁻¹ ^ (n - i)
        ≤ 1 * O'.valuation y⁻¹ ^ (n - i) := by gcongr; exact hcoef i
      _ < 1 := by
        rw [one_mul]
        exact pow_lt_one₀ zero_le' hyinv (Nat.sub_ne_zero_of_lt hi)
  have : O'.valuation (1 : F) < 1 := by
    rw [hone, Valuation.map_neg]; exact hlt
  rw [map_one] at this
  exact lt_irrefl _ this

theorem valuationSubring_eq_integralClosure_of_henselian
    {K F : Type} [Field K] [Field F] [Algebra K F] [FiniteDimensional K F] [Algebra.IsSeparable K F]
    (O : ValuationSubring K) [IsDiscreteValuationRing O] [HenselianLocalRing O]
    [Algebra O F] [IsScalarTower O K F]
    (O' : ValuationSubring F) (hO' : ∀ x : K, algebraMap K F x ∈ O' ↔ x ∈ O) :
    O'.toSubring = (integralClosure O F).toSubring ∧ Module.Finite O (integralClosure O F) ∧
      IsDiscreteValuationRing (integralClosure O F) := by
  classical
  haveI : IsFractionRing O K := inferInstance
  haveI hCfin : Module.Finite O (integralClosure O F) := IsIntegralClosure.finite O K F (integralClosure O F)
  haveI : IsDedekindDomain (integralClosure O F) := IsIntegralClosure.isDedekindDomain O K F (integralClosure O F)
  haveI : IsFractionRing (integralClosure O F) F := integralClosure.isFractionRing_of_finite_extension K F

  haveI : IsLocalRing (integralClosure O F) := isLocalRing_of_isDomain_of_moduleFinite (R := O) (S := integralClosure O F)
  have hinjF : Function.Injective (algebraMap O F) := by
    rw [IsScalarTower.algebraMap_eq O K F]
    exact (algebraMap K F).injective.comp (IsFractionRing.injective O K)
  have hinj : Function.Injective (algebraMap O (integralClosure O F)) := by
    intro a b h
    apply hinjF
    rw [IsScalarTower.algebraMap_apply O (integralClosure O F) F, IsScalarTower.algebraMap_apply O (integralClosure O F) F b, h]
  have hCnf : ¬ IsField (integralClosure O F) := by
    rw [← Algebra.IsIntegral.isField_iff_isField hinj]
    exact IsDiscreteValuationRing.not_isField O
  haveI hDVR : IsDiscreteValuationRing (integralClosure O F) :=
    ((IsDiscreteValuationRing.TFAE (integralClosure O F) hCnf).out 0 2).mpr (inferInstance : IsDedekindDomain (integralClosure O F))
  refine ⟨?_, hCfin, hDVR⟩
  have hCle : ∀ c : integralClosure O F, (c : F) ∈ O' := fun c => mem_of_isIntegral O O' hO' c.2

  let φ : integralClosure O F →+* O' :=
    { toFun := fun c => ⟨(c : F), hCle c⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hφ : ∀ c, ((φ c : O') : F) = (c : F) := fun _ => rfl
  let P : Ideal (integralClosure O F) := (IsLocalRing.maximalIdeal O').comap φ
  haveI hP : P.IsPrime := Ideal.comap_isPrime φ _
  have hPmem : ∀ c, c ∈ P ↔ O'.valuation (c : F) < 1 := by
    intro c
    rw [Ideal.mem_comap, ValuationSubring.valuation_lt_one_iff]
    rfl
  obtain ⟨ϖ₀, hϖ₀⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hϖ₀K0 : (ϖ₀ : K) ≠ 0 := fun h => hϖ₀.ne_zero (Subtype.ext h)
  have hϖ₀v : O'.valuation (algebraMap O F ϖ₀) < 1 := by

    rw [IsScalarTower.algebraMap_apply O K F, ValuationSubring.algebraMap_apply]
    by_contra hge
    rw [not_lt] at hge
    have hle : O'.valuation (algebraMap K F (ϖ₀ : K)) ≤ 1 := (O'.valuation_le_one_iff _).mpr ((hO' _).mpr ϖ₀.2)
    have heq : O'.valuation (algebraMap K F (ϖ₀ : K)) = 1 := le_antisymm hle hge
    have hinv : algebraMap K F (ϖ₀ : K)⁻¹ ∈ O' := by
      rw [← O'.valuation_le_one_iff, map_inv₀, map_inv₀, heq, inv_one]
    have hinvO : (ϖ₀ : K)⁻¹ ∈ O := (hO' _).mp hinv
    apply hϖ₀.not_isUnit
    exact ⟨⟨ϖ₀, ⟨(ϖ₀ : K)⁻¹, hinvO⟩, Subtype.ext (mul_inv_cancel₀ hϖ₀K0), Subtype.ext (inv_mul_cancel₀ hϖ₀K0)⟩, rfl⟩
  have hPne : P ≠ ⊥ := by
    intro h
    have hmem : algebraMap O (integralClosure O F) ϖ₀ ∈ P := by
      rw [hPmem]
      have : ((algebraMap O (integralClosure O F) ϖ₀ : integralClosure O F) : F) = algebraMap O F ϖ₀ :=
        (IsScalarTower.algebraMap_apply O (integralClosure O F) F ϖ₀).symm
      rw [this]; exact hϖ₀v
    rw [h, Ideal.mem_bot] at hmem
    exact hϖ₀.ne_zero (hinj (by rw [hmem, map_zero]))
  have hPmax : P = IsLocalRing.maximalIdeal (integralClosure O F) :=
    IsLocalRing.eq_maximalIdeal (hP.isMaximal hPne)

  apply le_antisymm
  · intro y hy
    change y ∈ integralClosure O F
    by_cases hy0 : y = 0
    · rw [hy0]; exact Subalgebra.zero_mem _
    haveI : ValuationRing (integralClosure O F) := inferInstance
    rcases ValuationRing.isInteger_or_isInteger (integralClosure O F) y with ⟨c, hc⟩ | ⟨c, hc⟩
    · rw [← hc]; exact c.2
    ·
      have hcF : (c : F) = y⁻¹ := hc
      by_cases hcu : IsUnit c
      · obtain ⟨d, hd⟩ := hcu.exists_right_inv
        have h2 : y⁻¹ * (d : F) = 1 := by
          have h3 := congrArg (fun z : integralClosure O F => (z : F)) hd
          simp only [Subalgebra.coe_mul, hcF, Subalgebra.coe_one] at h3
          exact h3
        have : (d : F) = y := by
          calc (d : F) = y * (y⁻¹ * d) := by rw [← mul_assoc, mul_inv_cancel₀ hy0, one_mul]
            _ = y := by rw [h2, mul_one]
        rw [← this]; exact d.2
      · exfalso
        have hcm : c ∈ IsLocalRing.maximalIdeal (integralClosure O F) := (IsLocalRing.mem_maximalIdeal _).mpr hcu
        rw [← hPmax, hPmem, hcF, map_inv₀, inv_lt_one₀ ((Valuation.pos_iff _).mpr hy0)] at hcm
        exact absurd ((O'.valuation_le_one_iff y).mpr hy) (not_le.mpr hcm)
  · intro y hy
    exact mem_of_isIntegral O O' hO' hy

end S17Hens

theorem solution
    {K F : Type} [Field K] [Field F] [Algebra K F] [FiniteDimensional K F] [Algebra.IsSeparable K F]
    (O : ValuationSubring K) [IsDiscreteValuationRing O] [HenselianLocalRing O]
    [Algebra O F] [IsScalarTower O K F]
    (O' : ValuationSubring F) (hO' : ∀ x : K, algebraMap K F x ∈ O' ↔ x ∈ O) :
    O'.toSubring = (integralClosure O F).toSubring ∧ Module.Finite O (integralClosure O F) ∧
      IsDiscreteValuationRing (integralClosure O F) :=
  S17Hens.valuationSubring_eq_integralClosure_of_henselian O O' hO'

end S_ValuationSubring_toSubring_eq_integralClosure_and_finite_and_isDiscreteValuationRing_of_henselian
end P2MW
export P2MW.S_ValuationSubring_toSubring_eq_integralClosure_and_finite_and_isDiscreteValuationRing_of_henselian (solution)
