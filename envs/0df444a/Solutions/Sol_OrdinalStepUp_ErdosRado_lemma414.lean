-- Prove2me | solution 1 for OrdinalStepUp.ErdosRado.lemma414
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:53:42.073595+00:00
-- url     : https://prove2.me/submissions/0abb68b8-67aa-4eb2-b706-373a0886c79c

import Mathlib.SetTheory.Cardinal.EventuallyConst
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic.FinCases
import Definitions.Def_OrdinalStepUp_Solution
import Theorems.Thm_OrdinalStepUp_ErdosRado_exists_wo_gt
import Theorems.Thm_OrdinalStepUp_ErdosRado_nextIn_mem
import Theorems.Thm_OrdinalStepUp_ErdosRado_wo_nextIn
import Theorems.Thm_OrdinalStepUp_ErdosRado_otpOrd_discNext_image
import Theorems.Thm_OrdinalStepUp_ErdosRado_exists_chain_discSeq

set_option autoImplicit true
open OrdinalStepUp OrdinalStepUp.ErdosRado
open Ordinal
universe u
variable {n r : ℕ} {α β κ μ θ : Ordinal} {a b c : SetOrd} {𝒜 ℬ 𝒞 : Set SetOrd}
  {V : Type u} {wo wo' : WellOrder} {x : wo.α}
namespace OrdinalStepUp.ErdosRado
theorem _root_.solution {𝒟 : Set SetOrd} (hD : IsIndec (otp 𝒟))
    (hup : ∀ a ∈ 𝒟, ∀ b ∈ 𝒟, ∀ c ∈ 𝒟, a ≺w b → b ≺w c → disc a b < disc b c)
    (g : Finset Ordinal → Set.Iio μ) (ι : Set.Iio μ)
    (hg : ∀ u : FinChain (n + 2), (∀ j, u j ∈ 𝒟) → g (sigmaOf u) = ι) :
    ∃ 𝒜 : SetOrd, otpOrd 𝒜 = otp 𝒟 ∧ 𝒜 ⊆ ⋃₀ 𝒟 ∧ Mono g (n + 1) 𝒜 ι := by
  refine ⟨discNext 𝒟 '' 𝒟, otpOrd_discNext_image hD hup, ?_, ?_⟩
  · -- A discrepancy lies in the symmetric difference of the two points it
    -- separates, so the transferred set never leaves `⋃₀ 𝒟`. This is what
    -- keeps the transfer inside `κ` when the points of `𝒟` are subsets of `κ`.
    rintro _ ⟨a, ha, rfl⟩
    have hex := exists_wo_gt hD ha
    rcases disc_mem_symmDiff (ne_of_irrefl (wo_nextIn hex)) with h | h
    · exact ⟨a, ha, h.1⟩
    · exact ⟨_, nextIn_mem hex, h.1⟩
  intro T hTA hTcard
  -- Enumerate `T` increasingly; `Ordinal` is linearly ordered, so this is direct.
  set w : Fin (n + 1) → Ordinal := ⇑(T.orderEmbOfFin hTcard) with hw
  have hwmono : StrictMono w := (T.orderEmbOfFin hTcard).strictMono
  have hwmem : ∀ i, w i ∈ discNext 𝒟 '' 𝒟 := (hTA  <|T.orderEmbOfFin_mem hTcard ·)
  obtain ⟨u, huD, hudisc⟩ := exists_chain_discSeq hD hup w hwmono hwmem
  -- `σ u` is exactly `T`, so the pulled-back colour is `g T`.
  have hsigma : sigmaOf u = T := by
    rw [sigmaOf, funext hudisc, hw]
    exact T.image_orderEmbOfFin_univ hTcard
  rw [← hsigma]
  exact hg u huD
end OrdinalStepUp.ErdosRado
