-- Prove2me | solution 1 for Subalgebra.exists_valuationSubring_mem_iff_of_isPrime_of_not_map_maximalIdeal_le_of_isAlgebraic_adjoin
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/ee29769b-6800-5e8c-9878-911dcf572eb2

import Mathlib
import Theorems.Thm_IsIntegrallyClosed_exists_valuationSubring_mem_iff_of_height_eq_one
import Theorems.Thm_Subalgebra_isMaximal_of_isPrime_of_ne_bot_of_isAlgebraic_adjoin_singleton
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Subalgebra_exists_valuationSubring_mem_iff_of_isPrime_of_not_map_maximalIdeal_le_of_isAlgebraic_adjoin

set_option autoImplicit false

open IsLocalRing

namespace GFV

variable {A : Type} [CommRing A] {F : Type} [Field F] [Algebra A F]

def locSub (B : Subalgebra A F) (𝔭 : Ideal ↥B) [𝔭.IsPrime] : Subalgebra A F where
  carrier := {f | ∃ b c : ↥B, c ∉ 𝔭 ∧ f * (c : F) = (b : F)}
  mul_mem' := by
    rintro f g ⟨b, c, hc, h⟩ ⟨b', c', hc', h'⟩
    refine ⟨b * b', c * c', fun hm => (‹𝔭.IsPrime›.mem_or_mem hm).elim hc hc', ?_⟩
    push_cast
    rw [← h, ← h']; ring
  one_mem' := ⟨1, 1, fun h1 => ‹𝔭.IsPrime›.ne_top ((Ideal.eq_top_iff_one 𝔭).mpr h1), by simp⟩
  add_mem' := by
    rintro f g ⟨b, c, hc, h⟩ ⟨b', c', hc', h'⟩
    refine ⟨b * c' + b' * c, c * c', fun hm => (‹𝔭.IsPrime›.mem_or_mem hm).elim hc hc', ?_⟩
    push_cast
    rw [← h, ← h']; ring
  zero_mem' := ⟨0, 1, fun h1 => ‹𝔭.IsPrime›.ne_top ((Ideal.eq_top_iff_one 𝔭).mpr h1), by simp⟩
  algebraMap_mem' := fun a =>
    ⟨algebraMap A ↥B a, 1, fun h1 => ‹𝔭.IsPrime›.ne_top ((Ideal.eq_top_iff_one 𝔭).mpr h1), by simp⟩

theorem mem_locSub_iff (B : Subalgebra A F) (𝔭 : Ideal ↥B) [𝔭.IsPrime] (f : F) :
    f ∈ locSub B 𝔭 ↔ ∃ b c : ↥B, c ∉ 𝔭 ∧ f * (c : F) = (b : F) := Iff.rfl

theorem le_locSub (B : Subalgebra A F) (𝔭 : Ideal ↥B) [𝔭.IsPrime] : B ≤ locSub B 𝔭 :=
  fun f hf => ⟨⟨f, hf⟩, 1, fun h1 => ‹𝔭.IsPrime›.ne_top ((Ideal.eq_top_iff_one 𝔭).mpr h1), by simp⟩

theorem isLocalization_locSub (B : Subalgebra A F) (𝔭 : Ideal ↥B) [𝔭.IsPrime] :
    letI : Algebra ↥B ↥(locSub B 𝔭) := (Subalgebra.inclusion (le_locSub B 𝔭)).toRingHom.toAlgebra
    IsLocalization.AtPrime ↥(locSub B 𝔭) 𝔭 := by
  letI : Algebra ↥B ↥(locSub B 𝔭) := (Subalgebra.inclusion (le_locSub B 𝔭)).toRingHom.toAlgebra
  have halg : ∀ b : ↥B, (algebraMap ↥B ↥(locSub B 𝔭) b : F) = (b : F) := fun b => rfl
  rw [IsLocalization.AtPrime, isLocalization_iff]
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨y, hy⟩
    have hy0 : (y : F) ≠ 0 := by
      intro h0
      apply hy
      have : y = 0 := Subtype.ext h0
      simp [this]
    have hinv : (y : F)⁻¹ ∈ locSub B 𝔭 := ⟨1, y, hy, by simp [hy0]⟩
    refine isUnit_iff_exists_inv.mpr ⟨⟨(y : F)⁻¹, hinv⟩, ?_⟩
    apply Subtype.ext
    show (algebraMap ↥B ↥(locSub B 𝔭) y : F) * (y : F)⁻¹ = 1
    rw [halg]; exact mul_inv_cancel₀ hy0
  · rintro ⟨z, b, c, hc, h⟩
    exact ⟨(b, ⟨c, hc⟩), Subtype.ext (by simpa [halg] using h)⟩
  · intro x y hxy
    refine ⟨1, ?_⟩
    have : (x : F) = (y : F) := by rw [← halg x, ← halg y, hxy]
    simpa using Subtype.ext this

end GFV

open GFV in
theorem solution
    {A₀ : Type} [CommRing A₀] [IsDomain A₀] [IsDiscreteValuationRing A₀]
    {F : Type} [Field F] [Algebra A₀ F]
    (B : Subalgebra A₀ F) (hBfg : B.FG)
    (hBn : ∀ x : F, IsIntegral ↥B x → x ∈ B)
    (hBfrac : ∀ x : F, ∃ b c : F, b ∈ B ∧ c ∈ B ∧ c ≠ 0 ∧ x * c = b)

    (t : F) (halg : ∀ x : F, IsAlgebraic ↥(Algebra.adjoin A₀ ({t} : Set F)) x)
    (𝔭 : Ideal ↥B) (h𝔭 : 𝔭.IsPrime) (h𝔭0 : 𝔭 ≠ ⊥)
    (hgen : ¬ (Ideal.map (algebraMap A₀ ↥B) (maximalIdeal A₀) ≤ 𝔭)) :
    ∃ V : ValuationSubring F, ∀ f : F, f ∈ V ↔ ∃ b c : ↥B, c ∉ 𝔭 ∧ f * (c : F) = (b : F) := by
  classical
  haveI : 𝔭.IsPrime := h𝔭

  haveI : IsNoetherianRing ↥B := isNoetherianRing_of_fg hBfg
  haveI : IsFractionRing ↥B F := by
    refine IsFractionRing.of_field (R := ↥B) (K := F) fun z => ?_
    obtain ⟨b, c, hb, hc, hc0, h⟩ := hBfrac z
    refine ⟨⟨b, hb⟩, ⟨c, hc⟩, ?_⟩
    change z = b / c
    rw [eq_div_iff hc0]; exact h
  haveI : IsIntegrallyClosed ↥B :=
    (isIntegrallyClosed_iff F).mpr fun {x} hx => ⟨⟨x, hBn x hx⟩, rfl⟩

  have hA : ∀ a : A₀, a ≠ 0 → algebraMap A₀ ↥B a ∉ 𝔭 := by
    intro a ha hmem
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible A₀
    obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.associated_pow_irreducible ha hϖ
    have hpow : (algebraMap A₀ ↥B ϖ) ^ n ∈ 𝔭 := by
      rw [← map_pow, ← hu, map_mul]
      exact Ideal.mul_mem_right _ _ hmem
    have hϖmem : algebraMap A₀ ↥B ϖ ∈ 𝔭 := Ideal.IsPrime.mem_of_pow_mem h𝔭 n hpow
    apply hgen
    rw [hϖ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton, Ideal.span_le]
    simpa using hϖmem

  let S : Subalgebra A₀ F := locSub B 𝔭
  have hS : ∀ a : A₀, algebraMap A₀ F a ≠ 0 → (algebraMap A₀ F a)⁻¹ ∈ S := by
    intro a ha
    have ha0 : a ≠ 0 := fun h0 => ha (by simp [h0])
    refine ⟨1, algebraMap A₀ ↥B a, hA a ha0, ?_⟩
    rw [Subalgebra.coe_algebraMap]
    simp [ha]
  haveI : Algebra.IsAlgebraic ↥(Algebra.adjoin A₀ ({t} : Set F)) F := ⟨halg⟩
  haveI hdim : Ring.KrullDimLE 1 ↥S := Ring.KrullDimLE.mk₁' fun P hP hPp => by
    haveI := hPp
    exact Subalgebra.isMaximal_of_isPrime_of_ne_bot_of_isAlgebraic_adjoin_singleton t S hS P hP

  letI : Algebra ↥B ↥S := (Subalgebra.inclusion (le_locSub B 𝔭)).toRingHom.toAlgebra
  haveI : IsLocalization.AtPrime ↥S 𝔭 := isLocalization_locSub B 𝔭
  have hle : ringKrullDim ↥S ≤ 1 := Ring.krullDimLE_iff.mp hdim
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height 𝔭 ↥S] at hle
  have hle' : 𝔭.height ≤ 1 := by exact_mod_cast hle
  have hne : 𝔭.height ≠ 0 := by
    rw [Ne, Ideal.height_eq_zero_iff, IsDomain.minimalPrimes_eq_singleton_bot]
    exact h𝔭0
  have hht : 𝔭.height = 1 := le_antisymm hle' (ENat.one_le_iff_ne_zero.mpr hne)

  obtain ⟨V, -, -, hV⟩ :=
    IsIntegrallyClosed.exists_valuationSubring_mem_iff_of_height_eq_one F 𝔭 hht
  exact ⟨V, fun f => hV f⟩

end S_Subalgebra_exists_valuationSubring_mem_iff_of_isPrime_of_not_map_maximalIdeal_le_of_isAlgebraic_adjoin
end P2MW
export P2MW.S_Subalgebra_exists_valuationSubring_mem_iff_of_isPrime_of_not_map_maximalIdeal_le_of_isAlgebraic_adjoin (solution)
