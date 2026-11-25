-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.kur_quad
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:48:47.0788+00:00
-- url     : https://prove2.me/submissions/c1ccfebd-52b7-47fa-b31d-c0abadabb9d3

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ExistsTeichmullerRepModPrime
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_KurNewton
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_NormSqrtNegPowPrimeSqSub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_kq_norm_l_lt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_kq_add_le
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_kq_add_lt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_kq_int_unit
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_kq_pow_l
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_kq_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
open Formalism.L2.Th1.CM
variable (l : ℕ) [Fact l.Prime]
variable {l}
variable (l)
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution (d : ℕ) (hd : d % 4 = 3) (hl : l ≠ 2) (hld : ¬ l ∣ d)
    (hin : ¬ ∃ a : ZMod l, a ^ 2 = -(d : ZMod l)) (a : ℂ_[l])
    (ha : a ^ 2 - a + (((d + 1) / 4 : ℕ) : ℂ_[l]) = 0) :
    ‖a‖ ≤ 1 ∧ ‖1 - 2 * a‖ = 1 ∧ ∃ ha' : a ∈ MaximalUnramifiedExtension l, ∀ σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l, FrobField (MaximalUnramifiedExtension l) l σ →
      σ ⟨a, ha'⟩ = 1 - ⟨a, ha'⟩ := by
  have h4 : (((d + 1) / 4 : ℕ) : ℂ_[l]) * 4 = (d : ℂ_[l]) + 1 := by
    have h44 : (d + 1) / 4 * 4 = d + 1 := by omega
    exact_mod_cast h44
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℂ_[l], δ = 1 - 2 * a := ⟨_, rfl⟩
  have hδ : δ ^ 2 = -(d : ℂ_[l]) := by
    rw [hδdef]
    linear_combination 4 * ha - h4
  have hd1 : ‖(d : ℂ_[l])‖ = 1 := by
    have hu := kq_int_unit l (d : ℤ) (by exact_mod_cast hld)
    exact_mod_cast hu
  have hn : ‖δ‖ = 1 := by
    have hh := congrArg norm hδ
    rw [norm_pow, norm_neg, hd1] at hh
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp hh
  have h2 : ‖(2 : ℂ_[l])‖ = 1 := by
    have hu := kq_int_unit l 2 (by
      intro h2d
      have h2n : l ∣ 2 := by exact_mod_cast h2d
      exact hl ((Nat.prime_dvd_prime_iff_eq (Fact.out : l.Prime) Nat.prime_two).mp h2n))
    exact_mod_cast hu
  have ha2 : a * 2 = 1 - δ := by
    rw [hδdef]
    ring
  have hna : ‖a‖ ≤ 1 := by
    have hh : ‖a‖ = ‖1 - δ‖ := by rw [← ha2, norm_mul, h2, mul_one]
    rw [hh, sub_eq_add_neg]
    exact kq_add_le l _ _ 1 (by simp) (by rw [norm_neg, hn])
  have hδK : δ ∈ MaximalUnramifiedExtension l := kq_mem d hl hld hin δ hδ hn
  have h2K : (2 : ℂ_[l]) ∈ MaximalUnramifiedExtension l := by simpa using natCast_mem (MaximalUnramifiedExtension l) 2
  have h20 : (2 : ℂ_[l]) ≠ 0 := two_ne_zero
  have haK : a ∈ MaximalUnramifiedExtension l := by
    have hh : a = (1 - δ) / 2 := by rw [eq_div_iff h20, ha2]
    rw [hh]
    exact div_mem (sub_mem (one_mem _) hδK) h2K
  refine ⟨hna, by rw [← hδdef]; exact hn, haK, fun σ hσ => ?_⟩
  obtain ⟨-, -, -, f4⟩ := hσ
  have hh : a = (1 - δ) / 2 := by rw [eq_div_iff h20, ha2]
  obtain ⟨D, hD⟩ : ∃ D : MaximalUnramifiedExtension l, (D : ℂ_[l]) = δ := ⟨⟨δ, hδK⟩, rfl⟩
  have hD2 : D ^ 2 = -((d : ℕ) : MaximalUnramifiedExtension l) := Subtype.ext (by simp [hD, hδ])
  have hDn : ‖D‖ = 1 := by
    rw [← hn, ← hD]
    rfl
  have hσD : σ D ^ 2 = D ^ 2 := by rw [← map_pow, hD2, map_neg, map_natCast]
  have hneg : σ D = -D := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hσD with h | h
    · exfalso
      have hf' : ‖δ - δ ^ l‖ ≤ ‖(l : ℂ_[l])‖ := by
        have h5 := f4 D (le_of_eq hDn)
        rw [h] at h5
        rw [← hD]
        exact h5
      have hsum : (2 : ℂ_[l]) * δ = (δ - δ ^ l) + (δ ^ l + δ) := by ring
      have h2d : ‖(2 : ℂ_[l]) * δ‖ = 1 := by rw [norm_mul, h2, hn, one_mul]
      have hlt := kq_add_lt l _ _ 1 (hf'.trans_lt (kq_norm_l_lt l))
        ((kq_pow_l d hl hld hin δ hδ hn).trans_lt (kq_norm_l_lt l))
      rw [← hsum, h2d] at hlt
      exact lt_irrefl 1 hlt
    · exact h
  have e2 : ((2 : MaximalUnramifiedExtension l) : ℂ_[l]) = 2 := by
    first
    | rfl
    | norm_cast
    | simp
  have hA2 : (⟨a, haK⟩ : MaximalUnramifiedExtension l) * 2 = 1 - D := by
    apply Subtype.ext
    show a * ((2 : MaximalUnramifiedExtension l) : ℂ_[l]) = ((1 - D : MaximalUnramifiedExtension l) : ℂ_[l])
    rw [e2, ha2, ← hD]
    rfl
  have h2ne : (2 : MaximalUnramifiedExtension l) ≠ 0 := fun h0 => h20 (by rw [← e2, h0]; rfl)
  have hs : σ ⟨a, haK⟩ * 2 = 1 + D := by
    have h6 := congrArg σ hA2
    rw [map_mul, map_ofNat, map_sub, map_one, hneg] at h6
    rw [h6]
    ring
  apply mul_right_cancel₀ h2ne
  rw [hs, sub_mul, hA2]
  ring
end ReciprocityTheory.ChartRestriction.L1
