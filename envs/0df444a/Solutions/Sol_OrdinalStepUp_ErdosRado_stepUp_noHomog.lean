-- Prove2me | solution 1 for OrdinalStepUp.ErdosRado.stepUp_noHomog
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:55:07.715648+00:00
-- url     : https://prove2.me/submissions/aa2c6672-e6a7-40ff-ad25-da7d161d30ae

import Mathlib.SetTheory.Cardinal.EventuallyConst
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic.FinCases
import Definitions.Def_OrdinalStepUp_Solution
import Theorems.Thm_OrdinalStepUp_ErdosRado_not_inK_of_inK01
import Theorems.Thm_OrdinalStepUp_ErdosRado_exists_homogeneous
import Theorems.Thm_OrdinalStepUp_ErdosRado_exists_all_disc_up
import Theorems.Thm_OrdinalStepUp_ErdosRado_mono_iff_chains
import Theorems.Thm_OrdinalStepUp_ErdosRado_lemma414
import Theorems.Thm_OrdinalStepUp_ErdosRado_not_inP01_of_inP0
import Theorems.Thm_OrdinalStepUp_ErdosRado_not_inP10_of_inP0
import Theorems.Thm_OrdinalStepUp_ErdosRado_not_inP10_of_inP01
import Theorems.Thm_OrdinalStepUp_ErdosRado_not_inK_of_inK10
import Theorems.Thm_OrdinalStepUp_ErdosRado_not_inK10_of_inK01
import Theorems.Thm_OrdinalStepUp_ErdosRado_no_pattern01_of_no_inK01
import Theorems.Thm_OrdinalStepUp_ErdosRado_no_pattern10_of_no_inK10
import Theorems.Thm_OrdinalStepUp_ErdosRado_up_forces_up_of_no_inP01
import Theorems.Thm_OrdinalStepUp_ErdosRado_down_forces_down_of_no_inP10
import Theorems.Thm_OrdinalStepUp_ErdosRado_chainOfFinset_toFinset
import Theorems.Thm_OrdinalStepUp_ErdosRado_inP0_of_allUp
import Theorems.Thm_P2M_OrdinalStepUp_ErdosRado_colour__ne_colour__9150ddf9722d

set_option autoImplicit true
open OrdinalStepUp OrdinalStepUp.ErdosRado
open Ordinal
universe u
variable {n r : ℕ} {α β κ μ θ : Ordinal} {a b c : SetOrd} {𝒜 ℬ 𝒞 : Set SetOrd}
  {V : Type u} {wo wo' : WellOrder} {x : wo.α}
namespace OrdinalStepUp.ErdosRado
theorem _root_.solution {g : Finset Ordinal → Set.Iio μ} (hμ : 1 < μ) (hθ : IsIndec θ)
    (hg : NoHomogOrd κ g (n + 3) (θ)) :
    NoHomog κ (stepUpColour (n := n) hμ g) (n + 4) θ := by
  intro 𝒜 hAκ hA ι hmono
  have hAi : IsIndec (otpOf WO 𝒜) := hA ▸ hθ
  rw [mono_iff_chains] at hmono
  -- Read the colouring off chains.
  open Classical in
  have hval {u : FinChain (n + 4)} (hu : ∀ j, u j ∈ 𝒜) :
      (if (InK01 ⊔ InP01) u then colour₁ hμ
       else if InP0 u then g (sigmaOf u) else colour₀ hμ) = ι := by
    have := hmono u hu
    rwa [stepUpColour, dif_pos u.card_toFinset, chainOfFinset_toFinset] at this
  -- The three values the colouring can take, read straight off `hval`.
  have hone {u : FinChain (n + 4)} (hu : ∀ j, u j ∈ 𝒜) (h : (InK01 ⊔ InP01) u) :
      colour₁ hμ = ι := by rw [← hval hu, if_pos h]
  have hzero {u : FinChain (n + 4)} (hu : ∀ j, u j ∈ 𝒜) (h : ¬ (InK01 ⊔ InP01) u)
      (h0 : ¬ InP0 u) : colour₀ hμ = ι := by rw [← hval hu, if_neg h, if_neg h0]
  have hgval {u : FinChain (n + 4)} (hu : ∀ j, u j ∈ 𝒜) (h : ¬ (InK01 ⊔ InP01) u)
      (h0 : InP0 u) : g (sigmaOf u) = ι := by rw [← hval hu, if_neg h, if_pos h0]
  -- The endgame, once `ℬ` is `K`-homogeneous and `𝒞 ⊆ ℬ` all-rising.
  have finish : ∀ ℬ 𝒞 : Set SetOrd, ℬ ⊆ 𝒜 → 𝒞 ⊆ ℬ → otp 𝒞 = θ → HomAgree ℬ →
      (∀ a ∈ 𝒞, ∀ b ∈ 𝒞, ∀ c ∈ 𝒞, a ≺w b → b ≺w c → disc a b < disc b c) → False := by
    intro ℬ 𝒞 hBA hCB hC homB hupC
    have hsig : ∀ u : FinChain (n + 4), (∀ j, u j ∈ 𝒞) → g (sigmaOf u) = ι := fun u hu =>
      have hP0 : InP0 u := inP0_of_allUp (homB.imp (·.mono hCB) (·.mono hCB)) hupC hu
      hgval (fun j => hBA (hCB (hu j))) (by
        rintro (hk | hp)
        · exact not_inK_of_inK01 hk hP0.1
        · exact not_inP01_of_inP0 hP0 hp) hP0
    obtain ⟨𝒜', hA', hsub, hmono'⟩ := lemma414 (n := n + 2) (hC ▸ hθ) hupC g ι hsig
    -- The transferred set is made of discrepancies between points of `𝒞 ⊆ 𝒜`,
    -- so it stays below `κ`, and the hypothesis downstairs applies to it.
    refine hg 𝒜' (fun ξ hξ => ?_) (hA'.trans hC) ι hmono'
    obtain ⟨a, ha, hξa⟩ := hsub hξ
    exact hAκ (hBA (hCB ha)) hξa
  by_cases hι : ι = colour₁ hμ
  · -- Colour `1`: avoid `K(1,0)`, then `P(1,0)`.
    subst hι
    have hK10 : ∀ u : FinChain (n + 4), (∀ j, u j ∈ 𝒜) → ¬ InK10 u := fun u hu h10 =>
      colour₀_ne_colour₁ hμ (hzero hu (by
        rintro (hk | hp)
        · exact not_inK10_of_inK01 hk h10
        · exact not_inK_of_inK10 h10 hp.1) (not_inK_of_inK10 h10 ·.1))
    obtain ⟨ℬ, hBA, hB, homB⟩ :=
      exists_homogeneous hAi (Or.inr (no_pattern10_of_no_inK10 hAi hK10))
    have hP10 : ∀ u : FinChain (n + 4), (∀ j, u j ∈ ℬ) → ¬ InP10 u := fun u hu h10 =>
      colour₀_ne_colour₁ hμ (hzero (fun j => hBA (hu j)) (by
        rintro (hk | hp)
        · exact not_inK_of_inK01 hk h10.1
        · exact not_inP10_of_inP01 hp h10) (not_inP10_of_inP0 · h10))
    obtain ⟨𝒞, hCB, hC, hupC⟩ :=
      exists_all_disc_up (hB ▸ hAi) homB
        (Or.inr (down_forces_down_of_no_inP10 (hB ▸ hAi) homB hP10))
    exact finish ℬ 𝒞 hBA hCB (hC.trans (hB.trans hA)) homB hupC
  · -- Any other colour: avoid `K(0,1)`, then `P(0,1)`.
    have hK01 : ∀ u : FinChain (n + 4), (∀ j, u j ∈ 𝒜) → ¬ InK01 u :=
      fun u hu h01 => hι (hone hu (Or.inl h01)).symm
    obtain ⟨ℬ, hBA, hB, homB⟩ :=
      exists_homogeneous hAi (Or.inl (no_pattern01_of_no_inK01 hAi hK01))
    have hP01 : ∀ u : FinChain (n + 4), (∀ j, u j ∈ ℬ) → ¬ InP01 u :=
      fun u hu h01 => hι (hone (fun j => hBA (hu j)) (Or.inr h01)).symm
    obtain ⟨𝒞, hCB, hC, hupC⟩ :=
      exists_all_disc_up (hB ▸ hAi) homB (Or.inl (up_forces_up_of_no_inP01 (hB ▸ hAi) homB hP01))
    exact finish ℬ 𝒞 hBA hCB (hC.trans (hB.trans hA)) homB hupC
end OrdinalStepUp.ErdosRado
