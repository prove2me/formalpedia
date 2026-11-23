-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__NZ_exc_of_dvd_c4fb5d0e0daf
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:03:22.953591+00:00
-- url     : https://prove2.me/submissions/d21da012-750d-40fd-9b54-ed9646314478

import Mathlib
import Definitions.Def_Formalism_CyclotomicNorms_StatementT
import Definitions.Def_Formalism_CyclotomicNorms_NonsquarefreeBounds_IrreducibilityOfRestriction
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NZTypeA
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_Equi_trans
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_succ_succ
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_succ_zero
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_zero_succ
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_zero_zero
import Theorems.Thm_P2M_Formalism_GaloisIrreducibility_BorderedIndexCases_zero_ne_succ__49ef2f236cb8
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GaloisIrreducibility.BorderedIndexCases.bord_succ_succ
attribute [local simp] Formalism.GaloisIrreducibility.BorderedIndexCases.bord_succ_zero
attribute [local simp] Formalism.GaloisIrreducibility.BorderedIndexCases.bord_zero_succ
attribute [local simp] Formalism.GaloisIrreducibility.BorderedIndexCases.bord_zero_zero
attribute [local simp] P2M_Formalism_GaloisIrreducibility_BorderedIndexCases_zero_ne_succ__49ef2f236cb8



set_option autoImplicit false
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.BasicNotions.Examples₂.NZ
open Polynomial Formalism.CyclotomicNorms
namespace Formalism.BasicNotions.Examples₂.NZ
theorem _root_.solution {g d e ℓ c : ℕ} (hg : 2 ≤ g) (hℓ : ℓ.Prime) (hd : 1 ≤ d) (he : 2 * Nat.gcd d e ≤ d)
    (h : g ^ d - 1 ∣ ℓ ^ c * (g ^ e - 1)) : Exc g d ℓ := by
  refine ⟨hℓ, ?_⟩
  set G := g ^ d with hG
  have hG3 : 3 ≤ G := by
    have h2 : 2 ≤ d := by
      have : 1 ≤ Nat.gcd d e := Nat.gcd_pos_of_pos_left e hd
      omega
    calc 3 ≤ 2 ^ 2 := by norm_num
      _ ≤ g ^ 2 := Nat.pow_le_pow_left hg 2
      _ ≤ g ^ d := Nat.pow_le_pow_right (by omega) h2
  have hn0 : G - 1 ≠ 0 := by omega
  have : Fact ℓ.Prime := ⟨hℓ⟩
  set v := padicValNat ℓ (G - 1) with hv
  have hfac : (G - 1).factorization ℓ = v := Nat.factorization_def _ hℓ
  set B := (G - 1) / ℓ ^ v with hB
  have hAB : ℓ ^ v * B = G - 1 := by
    have := Nat.ordProj_mul_ordCompl_eq_self (G - 1) ℓ
    rwa [hfac] at this
  have hcop : Nat.Coprime ℓ B := by
    have := Nat.coprime_ordCompl hℓ hn0
    rwa [hfac] at this
  have hB1 : B ∣ g ^ e - 1 :=
    (Nat.Coprime.pow_left c hcop).symm.dvd_of_dvd_mul_left ((Dvd.intro_left _ hAB).trans h)
  have hB2 : B ∣ g ^ Nat.gcd d e - 1 := by
    rw [← Nat.pow_sub_one_gcd_pow_sub_one]
    exact Nat.dvd_gcd (Dvd.intro_left _ hAB) hB1
  set s := Nat.gcd d e
  have hs1 : 1 ≤ s := Nat.gcd_pos_of_pos_left e hd
  have hgs : 2 ≤ g ^ s := le_trans hg (Nat.le_self_pow (by omega) g)
  have hBle : B ≤ g ^ s - 1 := Nat.le_of_dvd (by omega) hB2
  have hBsq : B * B ≤ G - 1 := by
    have h1 : g ^ s * g ^ s ≤ G := by
      rw [← pow_add, hG]; exact Nat.pow_le_pow_right (by omega) (by omega)
    have h2 : B * B ≤ (g ^ s - 1) * (g ^ s - 1) := Nat.mul_le_mul hBle hBle
    have h3 : (g ^ s - 1) * (g ^ s - 1) + 1 ≤ g ^ s * g ^ s := by
      obtain ⟨t, ht⟩ : ∃ t, g ^ s = t + 2 := ⟨g ^ s - 2, by omega⟩
      rw [ht]; simp only [show t + 2 - 1 = t + 1 by omega]; nlinarith
    omega
  set A := ℓ ^ v
  have hA2 : G - 1 ≤ A * A := by
    have h1 : (A * A) * (B * B) = (G - 1) * (G - 1) := by rw [← hAB]; ring
    by_contra hlt
    push Not at hlt
    have hBpos : 0 < B * B := by
      rcases Nat.eq_zero_or_pos (B * B) with h0 | h0
      · rw [h0, mul_zero] at h1
        have : 0 < (G - 1) * (G - 1) := Nat.mul_pos (by omega) (by omega)
        omega
      · exact h0
    have : (A * A) * (B * B) < (G - 1) * (G - 1) :=
      calc (A * A) * (B * B) < (G - 1) * (B * B) := Nat.mul_lt_mul_of_pos_right hlt hBpos
        _ ≤ (G - 1) * (G - 1) := Nat.mul_le_mul_left _ hBsq
    omega
  have hA4 : ℓ ^ (4 * v) = (A * A) * (A * A) := by
    show ℓ ^ (4 * v) = (ℓ ^ v * ℓ ^ v) * (ℓ ^ v * ℓ ^ v)
    rw [← pow_add, ← pow_add]; congr 1; ring
  rw [hA4]
  have h5 : (G - 1) * (G - 1) ≤ (A * A) * (A * A) := Nat.mul_le_mul hA2 hA2
  have h6 : G < (G - 1) * (G - 1) := by
    obtain ⟨t, ht⟩ : ∃ t, G = t + 3 := ⟨G - 3, by omega⟩
    rw [ht]; simp only [show t + 3 - 1 = t + 2 by omega]; nlinarith
  omega
end Formalism.BasicNotions.Examples₂.NZ
