-- Prove2me | solution 1 for PI.FockOneDegW.HwC.exists_wtvec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:02:13.868167+00:00
-- url     : https://prove2.me/submissions/2ee85ef2-4a3e-4dac-be17-482e0d04418c

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_CoeffXMulPderivSelf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_HighestWeightExists
import Theorems.Thm_PI_FockOneDegW_HwC_coeff_Ecc


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix FockH1Action MvPolynomial
open PI PI.FockOneDegW PI.FockOneDegW.HwC
open Classical
namespace PI.FockOneDegW.HwC
theorem _root_.solution {p q r s : ℕ} (U : Submodule ℂ (Pol p q r s))
    (hU : ∀ c : Ix p q, ∀ u ∈ U, fockAct1 p q r s (Eab c c) u ∈ U) :
    ∀ (n : ℕ) (u : Pol p q r s), u ∈ U → u ≠ 0 → (u.support.image wtv).card ≤ n →
      ∃ (ν : Ix p q → ℚ) (v : Pol p q r s), v ∈ U ∧ v ≠ 0 ∧ IsWt ν v ∧ v.support ⊆ u.support := by
  intro n
  induction n with
  | zero =>
    intro u _ hu0 hcard
    exfalso
    apply hu0
    have h0 := Nat.le_zero.1 hcard
    rw [Finset.card_eq_zero, Finset.image_eq_empty] at h0
    exact MvPolynomial.support_eq_empty.1 h0
  | succ n ih =>
    intro u hu hu0 hcard
    by_cases hall : ∀ β₁ ∈ u.support, ∀ β₂ ∈ u.support, wtv β₁ = wtv β₂
    · obtain ⟨β₀, hβ₀⟩ := Finset.nonempty_iff_ne_empty.2 (fun h => hu0 (MvPolynomial.support_eq_empty.1 h))
      exact ⟨wtv β₀, u, hu, hu0, fun β hβ c => by rw [hall β hβ β₀ hβ₀], subset_rfl⟩
    · push_neg at hall
      obtain ⟨β₁, h₁, β₂, h₂, hne⟩ := hall
      obtain ⟨c, hc⟩ := Function.ne_iff.1 hne

      have hcoeff : ∀ β, coeff β (fockAct1 p q r s (Eab c c) u - ((wtv β₁ c : ℚ) : ℂ) • u) =
          (((wtv β c : ℚ) : ℂ) - ((wtv β₁ c : ℚ) : ℂ)) * coeff β u := by
        intro β
        rw [coeff_sub, coeff_Ecc, coeff_smul, smul_eq_mul]
        ring
      have hsub : (fockAct1 p q r s (Eab c c) u - ((wtv β₁ c : ℚ) : ℂ) • u).support ⊆ u.support := by
        intro β hβ
        rw [MvPolynomial.mem_support_iff] at hβ ⊢
        intro h0
        apply hβ
        rw [hcoeff, h0, mul_zero]
      have hmem : fockAct1 p q r s (Eab c c) u - ((wtv β₁ c : ℚ) : ℂ) • u ∈ U :=
        U.sub_mem (hU c u hu) (U.smul_mem _ hu)
      have hβ₂ : β₂ ∈ (fockAct1 p q r s (Eab c c) u - ((wtv β₁ c : ℚ) : ℂ) • u).support := by
        rw [MvPolynomial.mem_support_iff, hcoeff]
        refine mul_ne_zero ?_ (MvPolynomial.mem_support_iff.1 h₂)
        rw [sub_ne_zero]
        exact_mod_cast (Ne.symm hc)
      have hne0 : fockAct1 p q r s (Eab c c) u - ((wtv β₁ c : ℚ) : ℂ) • u ≠ 0 := by
        intro h
        rw [h, MvPolynomial.support_zero] at hβ₂
        simp at hβ₂
      have himg : (fockAct1 p q r s (Eab c c) u - ((wtv β₁ c : ℚ) : ℂ) • u).support.image wtv ⊆
          (u.support.image wtv).erase (wtv β₁) := by
        intro w hw
        obtain ⟨β, hβ, rfl⟩ := Finset.mem_image.1 hw
        refine Finset.mem_erase.2 ⟨fun heq => ?_, Finset.mem_image_of_mem _ (hsub hβ)⟩
        have h0 : coeff β (fockAct1 p q r s (Eab c c) u - ((wtv β₁ c : ℚ) : ℂ) • u) = 0 := by
          rw [hcoeff, heq, sub_self, zero_mul]
        exact (MvPolynomial.mem_support_iff.1 hβ) h0
      have hcard' : ((fockAct1 p q r s (Eab c c) u - ((wtv β₁ c : ℚ) : ℂ) • u).support.image wtv).card ≤ n := by
        have h1 := Finset.card_le_card himg
        have h2 := Finset.card_erase_of_mem (Finset.mem_image_of_mem wtv h₁)
        omega
      obtain ⟨ν, v, hv, hv0, hvw, hvs⟩ := ih _ hmem hne0 hcard'
      exact ⟨ν, v, hv, hv0, hvw, hvs.trans hsub⟩
end PI.FockOneDegW.HwC
