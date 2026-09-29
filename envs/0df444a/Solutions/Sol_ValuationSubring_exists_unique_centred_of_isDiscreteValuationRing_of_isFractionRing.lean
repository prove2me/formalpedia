-- Prove2me | solution 1 for ValuationSubring.exists_unique_centred_of_isDiscreteValuationRing_of_isFractionRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/0115a6ae-e1d5-5c7d-82a6-33048203a8ec

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_exists_unique_centred_of_isDiscreteValuationRing_of_isFractionRing

set_option autoImplicit false

namespace DvrInterface

variable {F : Type*} [Field F]

theorem mem_nonunits_iff' (A : ValuationSubring F) (x : F) :
    x ∈ A.nonunits ↔ x ∈ A ∧ (x = 0 ∨ x⁻¹ ∉ A) := by
  rw [ValuationSubring.mem_nonunits_iff]
  by_cases hx : x = 0
  · subst hx
    simp [A.zero_mem]
  · constructor
    · intro h
      refine ⟨(A.valuation_le_one_iff x).mp h.le, Or.inr ?_⟩
      intro hinv
      have h1 : A.valuation x⁻¹ ≤ 1 := (A.valuation_le_one_iff _).mpr hinv
      rw [map_inv₀] at h1
      have hx' : A.valuation x ≠ 0 := (map_ne_zero _).mpr hx
      have : 1 ≤ A.valuation x := by
        rwa [inv_le_one₀ (zero_lt_iff.mpr hx')] at h1
      exact absurd h (not_lt.mpr this)
    · rintro ⟨-, h0 | hinv⟩
      · exact absurd h0 hx
      · by_contra hlt
        apply hinv
        rw [← A.valuation_le_one_iff, map_inv₀]
        have hx' : A.valuation x ≠ 0 := (map_ne_zero _).mpr hx
        rw [inv_le_one₀ (zero_lt_iff.mpr hx')]
        exact not_lt.mp hlt

theorem mul_mem_nonunits (A : ValuationSubring F) {x y : F} (hx : x ∈ A) (hy : y ∈ A.nonunits) :
    x * y ∈ A.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff] at hy ⊢
  rw [map_mul]
  calc A.valuation x * A.valuation y ≤ 1 * A.valuation y := by
        exact mul_le_mul_left ((A.valuation_le_one_iff x).mpr hx) _
    _ = A.valuation y := one_mul _
    _ < 1 := hy

theorem inv_mem_of_mem_of_not_mem_nonunits (A : ValuationSubring F) {x : F} (hx : x ∈ A)
    (hx' : x ∉ A.nonunits) : x⁻¹ ∈ A := by
  rw [mem_nonunits_iff'] at hx'
  push_neg at hx'
  exact (hx' hx).2

end DvrInterface

open DvrInterface in

theorem solution
    {B : Type*} [CommRing B] {F : Type*} [Field F]
    (ρ : B →+* F) (𝔶 : Ideal B) [𝔶.IsMaximal] (hker : RingHom.ker ρ ≤ 𝔶)
    (R : Subring F)
    (hR : ∀ x : F, x ∈ R ↔ ∃ s t : B, t ∉ 𝔶 ∧ x * ρ t = ρ s)
    (hdvr : IsDiscreteValuationRing ↥R) (hfrac : IsFractionRing ↥R F) :
    ∃ P : ValuationSubring F,
      (∀ s : B, ρ s ∈ P) ∧
      (∀ s : B, ρ s ∈ P.nonunits ↔ s ∈ 𝔶) ∧
      (∀ P' : ValuationSubring F,
        (∀ s : B, ρ s ∈ P') → (∀ s : B, ρ s ∈ P'.nonunits ↔ s ∈ 𝔶) → P' = P) ∧
      (∀ e : ↥P, ∃ s : B, (e : F) - ρ s ∈ P.nonunits) ∧
      IsPrincipalIdealRing ↥P := by
  classical
  haveI := hdvr
  haveI := hfrac
  have h𝔶top : 𝔶 ≠ ⊤ := Ideal.IsMaximal.ne_top inferInstance
  have h1 : (1 : B) ∉ 𝔶 := fun h => h𝔶top ((Ideal.eq_top_iff_one _).mpr h)

  have hρR : ∀ s : B, ρ s ∈ R := fun s => (hR _).mpr ⟨s, 1, h1, by rw [map_one, mul_one]⟩
  have hρne : ∀ t : B, t ∉ 𝔶 → ρ t ≠ 0 := fun t ht h0 => ht (hker (by rwa [RingHom.mem_ker]))
  have hinvR : ∀ t : B, t ∉ 𝔶 → (ρ t)⁻¹ ∈ R := fun t ht =>
    (hR _).mpr ⟨1, t, ht, by rw [inv_mul_cancel₀ (hρne t ht), map_one]⟩

  have hval : ∀ x : F, x ∈ R ∨ x⁻¹ ∈ R := by
    intro x
    rcases ValuationRing.isInteger_or_isInteger (↥R) x with ⟨r, hr⟩ | ⟨r, hr⟩
    · left; rw [← hr]; exact r.2
    · right; rw [← hr]; exact r.2
  let P : ValuationSubring F := ⟨R, hval⟩
  have hPmem : ∀ x : F, x ∈ P ↔ x ∈ R := fun x => Iff.rfl

  have hcen : ∀ s : B, ρ s ∈ P.nonunits ↔ s ∈ 𝔶 := by
    intro s
    rw [mem_nonunits_iff']
    constructor
    · rintro ⟨-, h0 | hinv⟩
      · exact hker (by rwa [RingHom.mem_ker])
      · by_contra hs
        exact hinv ((hPmem _).mpr (hinvR s hs))
    · intro hs
      refine ⟨(hPmem _).mpr (hρR s), ?_⟩
      by_cases h0 : ρ s = 0
      · exact Or.inl h0
      · right
        intro hinv
        obtain ⟨s', t', ht', he⟩ := (hR _).mp ((hPmem _).mp hinv)

        have : ρ (t' - s * s') = 0 := by
          rw [map_sub, map_mul, ← he, ← mul_assoc, mul_inv_cancel₀ h0, one_mul, sub_self]
        have hmem : t' - s * s' ∈ 𝔶 := hker (by rwa [RingHom.mem_ker])
        apply ht'
        have := 𝔶.add_mem hmem (𝔶.mul_mem_right s' hs)
        simpa using this

  have hex : ∃ s₀ : B, s₀ ∈ 𝔶 ∧ ρ s₀ ≠ 0 := by
    by_contra hno
    push_neg at hno
    apply IsDiscreteValuationRing.not_isField (↥R)
    refine ⟨⟨0, 1, zero_ne_one⟩, mul_comm, ?_⟩
    intro a ha
    obtain ⟨s, t, ht, he⟩ := (hR _).mp a.2
    have hs : s ∉ 𝔶 := by
      intro hs
      apply ha
      apply Subtype.ext
      have : (a : F) * ρ t = 0 := by rw [he, hno s hs]
      rcases mul_eq_zero.mp this with h | h
      · exact h
      · exact absurd h (hρne t ht)
    refine ⟨⟨ρ t * (ρ s)⁻¹, R.mul_mem (hρR t) (hinvR s hs)⟩, Subtype.ext ?_⟩
    show (a : F) * (ρ t * (ρ s)⁻¹) = 1
    rw [← mul_assoc, he, mul_inv_cancel₀ (hρne s hs)]
  obtain ⟨s₀, hs₀, hs₀ne⟩ := hex
  refine ⟨P, fun s => (hPmem _).mpr (hρR s), hcen, ?_, ?_, ?_⟩
  ·
    intro P' hP' hcen'

    have hle : P ≤ P' := by
      intro x hx
      obtain ⟨s, t, ht, he⟩ := (hR _).mp ((hPmem _).mp hx)
      have htinv : (ρ t)⁻¹ ∈ P' :=
        inv_mem_of_mem_of_not_mem_nonunits P' (hP' t) (fun h => ht ((hcen' t).mp h))
      have : x = ρ s * (ρ t)⁻¹ := by
        rw [← he, mul_assoc, mul_inv_cancel₀ (hρne t ht), mul_one]
      rw [this]
      exact P'.mul_mem _ _ (hP' s) htinv

    refine le_antisymm ?_ hle
    intro x hx
    by_contra hxR
    have hx0 : x ≠ 0 := fun h => hxR (h ▸ P.zero_mem)
    have hxinv : x⁻¹ ∈ R := (hval x).resolve_left hxR

    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (↥R)
    have hxi0 : (⟨x⁻¹, hxinv⟩ : ↥R) ≠ 0 := fun h => by
      have := congrArg Subtype.val h
      exact inv_ne_zero hx0 this
    obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hxi0 hϖ
    have hn : n ≠ 0 := by
      rintro rfl
      rw [pow_zero, mul_one] at hu

      apply hxR
      have : x = ((u⁻¹ : (↥R)ˣ) : ↥R) := by
        have h1 : (x⁻¹ : F) = ((u : ↥R) : F) := congrArg Subtype.val hu
        have h2 : ((u : ↥R) : F) * (((u⁻¹ : (↥R)ˣ) : ↥R) : F) = 1 := by
          rw [← Subring.coe_mul, Units.mul_inv]; rfl
        calc x = x * (((u : ↥R) : F) * (((u⁻¹ : (↥R)ˣ) : ↥R) : F)) := by rw [h2, mul_one]
          _ = (x * x⁻¹) * (((u⁻¹ : (↥R)ˣ) : ↥R) : F) := by rw [h1, mul_assoc]
          _ = _ := by rw [mul_inv_cancel₀ hx0, one_mul]
      rw [this]
      exact Subtype.mem _

    have hs₀R : (⟨ρ s₀, hρR s₀⟩ : ↥R) ≠ 0 := fun h => hs₀ne (congrArg Subtype.val h)
    obtain ⟨m, v, hv⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hs₀R hϖ

    have hpow : (x⁻¹) ^ m = ρ s₀ * ((((v⁻¹ : (↥R)ˣ) : ↥R) * (u : ↥R) ^ m * ϖ ^ (n * m - m) : ↥R) : F) := by
      have key : ((⟨x⁻¹, hxinv⟩ : ↥R)) ^ m =
          ⟨ρ s₀, hρR s₀⟩ * (((v⁻¹ : (↥R)ˣ) : ↥R) * (u : ↥R) ^ m * ϖ ^ (n * m - m)) := by
        rw [hu, hv, mul_pow, ← pow_mul]
        have hnm : n * m = m + (n * m - m) := by
          have : m ≤ n * m := Nat.le_mul_of_pos_left m (Nat.pos_of_ne_zero hn)
          omega
        conv_lhs => rw [hnm, pow_add]
        rw [show ((v : ↥R) * ϖ ^ m) * (((v⁻¹ : (↥R)ˣ) : ↥R) * (u : ↥R) ^ m * ϖ ^ (n * m - m)) =
            ((v : ↥R) * ((v⁻¹ : (↥R)ˣ) : ↥R)) * ((u : ↥R) ^ m * (ϖ ^ m * ϖ ^ (n * m - m))) by ring]
        rw [Units.mul_inv, one_mul]
      have := congrArg Subtype.val key
      simpa only [Subring.coe_mul, SubmonoidClass.coe_pow] using this

    have hunit : (x⁻¹) ^ m ∉ P'.nonunits := by
      rw [mem_nonunits_iff']
      push_neg
      intro _
      refine ⟨pow_ne_zero _ (inv_ne_zero hx0), ?_⟩
      rw [← inv_pow, inv_inv]
      exact P'.pow_mem hx m
    apply hunit
    rw [hpow, mul_comm]
    exact mul_mem_nonunits P' (hle (Subtype.mem _)) ((hcen' s₀).mpr hs₀)
  ·
    intro e
    obtain ⟨s, t, ht, he⟩ := (hR _).mp ((hPmem _).mp e.2)
    obtain ⟨t', i, hi, hti⟩ := Ideal.IsMaximal.exists_inv inferInstance ht
    refine ⟨s * t', ?_⟩
    have : (e : F) - ρ (s * t') = (e : F) * ρ i := by
      have h2 : ρ t * ρ t' = 1 - ρ i := by
        rw [← map_mul, ← map_one ρ, ← map_sub, ← hti]; ring_nf
      calc (e : F) - ρ (s * t') = (e : F) - (e : F) * ρ t * ρ t' := by rw [map_mul, ← he]
        _ = (e : F) - (e : F) * (ρ t * ρ t') := by ring
        _ = (e : F) * ρ i := by rw [h2]; ring
    rw [this]
    exact mul_mem_nonunits P e.2 ((hcen i).mpr hi)
  ·
    exact hdvr.toIsPrincipalIdealRing

end S_ValuationSubring_exists_unique_centred_of_isDiscreteValuationRing_of_isFractionRing
end P2MW
export P2MW.S_ValuationSubring_exists_unique_centred_of_isDiscreteValuationRing_of_isFractionRing (solution)
