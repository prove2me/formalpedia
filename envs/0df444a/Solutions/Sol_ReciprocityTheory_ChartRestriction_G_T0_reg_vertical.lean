-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.reg_vertical
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:27:04.85038+00:00
-- url     : https://prove2.me/submissions/3f6d793c-4040-46da-8276-1257dc554725

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_RegAVpt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_RegVert
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_regVert_eq_of_le_height_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_regVert_valuationRing
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_av_point


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open IsLocalRing
namespace ReciprocityTheory.ChartRestriction.G.T0
theorem _root_.solution {O A : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O] [CharZero O]
    [CommRing A] [IsDomain A] [Algebra O A] [Algebra.FiniteType O A] [Module.Flat O A]
    [IsIntegrallyClosed A] (f : FractionRing A)
    (hf : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Algebra O V]
      [Module.Finite O V] (φ : A →ₐ[O] V) (a b : A),
      f * algebraMap A (FractionRing A) b = algebraMap A (FractionRing A) a → φ b ≠ 0 →
      ∃ v : V, φ a = v * φ b)
    (P : Ideal A) [P.IsPrime] (hP : P.height = 1)
    (hv : Ideal.map (algebraMap O A) (maximalIdeal O) ≤ P) :
    ∃ a s : A, s ∉ P ∧ f * algebraMap A (FractionRing A) s = algebraMap A (FractionRing A) a := by
  classical
  by_contra hno
  haveI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing O A
  haveI : ValuationRing (Localization.AtPrime P) := regVert_valuationRing P hP
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hϖm : ϖ ∈ maximalIdeal O := (IsLocalRing.mem_maximalIdeal ϖ).2 hϖ.not_isUnit
  have hϖ0 : ϖ ≠ 0 := hϖ.ne_zero
  have hinjOA : Function.Injective (algebraMap O A) := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    by_contra hx0
    have hfl := (Module.Flat.flat_iff_torsion_eq_bot_of_isBezout (R := O) (M := A)).1 inferInstance
    have h1 : (1 : A) ∈ Submodule.torsion O A :=
      (Submodule.mem_torsion_iff _).2 ⟨⟨x, mem_nonZeroDivisors_of_ne_zero hx0⟩, by
        simp [Algebra.smul_def, hx]⟩
    rw [hfl] at h1
    exact one_ne_zero ((Submodule.mem_bot O).1 h1)
  have ht0 : algebraMap O A ϖ ≠ 0 := fun h => hϖ0 (hinjOA (by rw [h, map_zero]))
  have htP : algebraMap O A ϖ ∈ P := hv (Ideal.mem_map_of_mem _ hϖm)
  have hmin : P ∈ (Ideal.span {algebraMap O A ϖ}).minimalPrimes := by
    refine ⟨⟨inferInstance, (Ideal.span_singleton_le_iff_mem _).2 htP⟩, fun Q hQ hQP => ?_⟩
    haveI := hQ.1
    have hQ0 : Q ≠ ⊥ := fun h => ht0 (by
      have := hQ.2 (Ideal.mem_span_singleton_self (algebraMap O A ϖ)); rw [h] at this; exact this)
    exact (regVert_eq_of_le_height_one hQ0 hQP hP).symm.le
  obtain ⟨p, q, hq, hpq⟩ := IsFractionRing.div_surjective (A := A) f
  have hq0 : q ≠ 0 := nonZeroDivisors.ne_zero hq
  have hqK : algebraMap A (FractionRing A) q ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hq
  have hfq : f * algebraMap A (FractionRing A) q = algebraMap A (FractionRing A) p := by
    rw [← hpq, div_mul_cancel₀ _ hqK]
  have hinjAR : Function.Injective (algebraMap A (Localization.AtPrime P)) :=
    IsLocalization.injective (Localization.AtPrime P) P.primeCompl_le_nonZeroDivisors
  have key : ∀ d : Localization.AtPrime P,
      algebraMap A (Localization.AtPrime P) q * d = algebraMap A (Localization.AtPrime P) p → False := by
    intro d hd
    obtain ⟨⟨a, s⟩, hcs⟩ := IsLocalization.surj P.primeCompl d
    simp only at hcs
    apply hno
    refine ⟨a, s, s.2, ?_⟩
    have h3 : algebraMap A (Localization.AtPrime P) (q * a) = algebraMap A (Localization.AtPrime P) (p * s) := by
      rw [map_mul, map_mul, ← hd, mul_assoc, hcs]
    have h2 := hinjAR h3
    apply mul_left_cancel₀ hqK
    calc algebraMap A (FractionRing A) q * (f * algebraMap A (FractionRing A) s)
        = (f * algebraMap A (FractionRing A) q) * algebraMap A (FractionRing A) s := by ring
      _ = algebraMap A (FractionRing A) (p * s) := by rw [hfq, map_mul]
      _ = algebraMap A (FractionRing A) (q * a) := by rw [h2]
      _ = _ := by rw [map_mul]
  obtain ⟨c, hc | hc⟩ := ValuationRing.cond (algebraMap A (Localization.AtPrime P) q)
    (algebraMap A (Localization.AtPrime P) p)
  · exact key c hc
  have hcm : c ∈ maximalIdeal (Localization.AtPrime P) := by
    by_contra hcu
    have hu : IsUnit c := by
      by_contra h
      exact hcu ((IsLocalRing.mem_maximalIdeal c).2 h)
    refine key (↑hu.unit⁻¹) ?_
    rw [← hc, mul_assoc, IsUnit.mul_val_inv, mul_one]
  have hrad := IsLocalization.AtPrime.radical_map_of_mem_minimalPrimes (A := Localization.AtPrime P)
    P _ hmin
  rw [Localization.AtPrime.map_eq_maximalIdeal] at hrad
  have hc' : c ∈ (Ideal.map (algebraMap A (Localization.AtPrime P))
      (Ideal.span {algebraMap O A ϖ})).radical := hrad ▸ hcm
  obtain ⟨n, hn⟩ := hc'
  rw [Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton'] at hn
  obtain ⟨z, hz⟩ := hn
  let S : Subalgebra A (Localization.AtPrime P) := Algebra.adjoin A {z}
  haveI : Algebra.FiniteType A S := (Subalgebra.fg_iff_finiteType S).1 (by
    simpa using Subalgebra.fg_adjoin_finset (R := A) ({z} : Finset (Localization.AtPrime P)))
  haveI : Algebra.FiniteType O S := Algebra.FiniteType.trans (S := A) inferInstance inferInstance
  have hinjOR : Function.Injective (algebraMap O (Localization.AtPrime P)) := by
    rw [IsScalarTower.algebraMap_eq O A (Localization.AtPrime P)]; exact hinjAR.comp hinjOA
  have hcoe : ∀ x : O, ((algebraMap O S x : S) : Localization.AtPrime P) =
      algebraMap O (Localization.AtPrime P) x := fun x => rfl
  haveI : FaithfulSMul O S := (faithfulSMul_iff_algebraMap_injective O S).2 (by
    intro x y hxy
    apply hinjOR
    rw [← hcoe, ← hcoe, hxy])
  have hsp : Ideal.map (algebraMap O S) (maximalIdeal O) ≠ ⊤ := by
    intro htop
    have h2 : Ideal.map (S.val : S →+* Localization.AtPrime P)
        (Ideal.map (algebraMap O S) (maximalIdeal O)) ≤ maximalIdeal (Localization.AtPrime P) := by
      rw [Ideal.map_map, Ideal.map_le_iff_le_comap]
      intro x hx
      rw [Ideal.mem_comap, RingHom.comp_apply]
      have : (S.val : S →+* Localization.AtPrime P) (algebraMap O S x) =
          algebraMap A (Localization.AtPrime P) (algebraMap O A x) := by
        rw [← IsScalarTower.algebraMap_apply]; rfl
      rw [this]
      exact (IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime P) P _).2
        (hv (Ideal.mem_map_of_mem _ hx))
    rw [htop, Ideal.map_top] at h2
    exact (maximalIdeal.isMaximal (Localization.AtPrime P)).ne_top (top_le_iff.1 h2)
  have hqS : algebraMap A S q ≠ 0 := by
    intro h0
    apply hq0; apply hinjAR
    rw [map_zero]
    exact congrArg Subtype.val h0
  obtain ⟨V, _, _, _, _, _, φ, hφ⟩ := av_point (O := O) (B := S) hsp (algebraMap A S q) hqS
  obtain ⟨w, hw⟩ := hf V (φ.comp (IsScalarTower.toAlgHom O A S)) p q hfq hφ
  have hzS : z ∈ S := Algebra.subset_adjoin (Set.mem_singleton z)
  have hrel : (algebraMap A S q) ^ n = (algebraMap A S p) ^ n * (⟨z, hzS⟩ * algebraMap O S ϖ) := by
    apply Subtype.ext
    rw [SubmonoidClass.coe_pow, MulMemClass.coe_mul, SubmonoidClass.coe_pow, MulMemClass.coe_mul]
    change (algebraMap A (Localization.AtPrime P) q) ^ n =
      (algebraMap A (Localization.AtPrime P) p) ^ n * (z * algebraMap O (Localization.AtPrime P) ϖ)
    rw [IsScalarTower.algebraMap_apply O A (Localization.AtPrime P) ϖ, hz, ← hc, mul_pow]
  have h1 := congrArg φ hrel
  rw [map_pow, map_mul, map_pow, map_mul, AlgHom.commutes] at h1
  have hw' : φ (algebraMap A S p) = w * φ (algebraMap A S q) := hw
  rw [hw', mul_pow] at h1
  have hunit : IsUnit (algebraMap O V ϖ) := by
    refine IsUnit.of_mul_eq_one (w ^ n * φ ⟨z, hzS⟩) ?_
    have hQ : φ (algebraMap A S q) ^ n ≠ 0 := pow_ne_zero _ hφ
    apply mul_left_cancel₀ hQ
    linear_combination -h1
  have hmax := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := O) (maximalIdeal V)
  have heq : Ideal.comap (algebraMap O V) (maximalIdeal V) = maximalIdeal O :=
    IsLocalRing.eq_maximalIdeal hmax
  have hmV : algebraMap O V ϖ ∈ maximalIdeal V := by
    rw [← Ideal.mem_comap, heq]; exact hϖm
  exact (IsLocalRing.mem_maximalIdeal _).1 hmV hunit
end ReciprocityTheory.ChartRestriction.G.T0
