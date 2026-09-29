-- Prove2me | solution 1 for ValuationSubring.smul_eq_and_forall_smul_sub_mem_nonunits_of_mem_inertia
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/0bb9804f-d83d-56fb-a4c6-261948a884ca

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_smul_eq_and_forall_smul_sub_mem_nonunits_of_mem_inertia

set_option autoImplicit false

open scoped Pointwise

namespace InertStab

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

variable {G : Type*} [Group G] [MulSemiringAction G F]

theorem mem_nonunits_pointwise_smul_iff (g : G) (A : ValuationSubring F) (x : F) :
    x ∈ (g • A).nonunits ↔ g⁻¹ • x ∈ A.nonunits := by
  rw [mem_nonunits_iff', mem_nonunits_iff', ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem,
    ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, smul_inv'', smul_eq_zero_iff_eq]

end InertStab

open InertStab in

theorem solution
    {B : Type*} [CommRing B] {F : Type*} [Field F] {G : Type*} [Group G]
    [MulSemiringAction G B] [MulSemiringAction G F]
    (ρ : B →+* F) (hρ : ∀ (g : G) (b : B), g • ρ b = ρ (g • b))
    (𝔶 : Ideal B) (P : ValuationSubring F)
    (hP : ∀ b : B, ρ b ∈ P) (hPy : ∀ b : B, ρ b ∈ P.nonunits ↔ b ∈ 𝔶)
    (huniq : ∀ P' : ValuationSubring F,
      (∀ b : B, ρ b ∈ P') → (∀ b : B, ρ b ∈ P'.nonunits ↔ b ∈ 𝔶) → P' = P)
    (hres : ∀ e : ↥P, ∃ b : B, (e : F) - ρ b ∈ P.nonunits)
    (g : G) (hg : g ∈ 𝔶.inertia G) :
    g • P = P ∧ ∀ e : ↥P, g • (e : F) - e ∈ P.nonunits := by
  have hg' : g⁻¹ ∈ 𝔶.inertia G := inv_mem hg

  have hmem : ∀ (h : G), h ∈ 𝔶.inertia G → ∀ b : B, h • b ∈ 𝔶 ↔ b ∈ 𝔶 := by
    intro h hh b
    have hsub : h • b - b ∈ 𝔶 := hh b
    constructor
    · intro hb
      have := 𝔶.sub_mem hb hsub
      simpa using this
    · intro hb
      have := 𝔶.add_mem hsub hb
      simpa using this
  have hfix : g • P = P := by
    refine huniq (g • P) (fun b => ?_) (fun b => ?_)
    · rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, hρ]
      exact hP _
    · rw [mem_nonunits_pointwise_smul_iff, hρ, hPy, hmem g⁻¹ hg']
  have hρb : ∀ b : B, g • ρ b - ρ b ∈ P.nonunits := fun b => by
    rw [hρ, ← map_sub]
    exact (hPy _).mpr (hg b)

  have hsmul : ∀ x : F, x ∈ P.nonunits → g • x ∈ P.nonunits := by
    intro x hx
    have : g • x ∈ (g • P).nonunits := by
      rw [mem_nonunits_pointwise_smul_iff, inv_smul_smul]
      exact hx
    rwa [hfix] at this
  refine ⟨hfix, fun e => ?_⟩
  obtain ⟨b, hb⟩ := hres e
  have h1 : g • ((e : F) - ρ b) ∈ P.nonunits := hsmul _ hb
  have h2 : -((e : F) - ρ b) ∈ P.nonunits := neg_mem hb
  have hsum := add_mem (add_mem h1 (hρb b)) h2
  have heq : g • ((e : F) - ρ b) + (g • ρ b - ρ b) + -((e : F) - ρ b) = g • (e : F) - e := by
    rw [smul_sub]; ring
  rwa [heq] at hsum

end S_ValuationSubring_smul_eq_and_forall_smul_sub_mem_nonunits_of_mem_inertia
end P2MW
export P2MW.S_ValuationSubring_smul_eq_and_forall_smul_sub_mem_nonunits_of_mem_inertia (solution)
