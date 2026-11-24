-- Prove2me | solution 1 for OrdinalStepUp.ErdosRado.discNext_strictMono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:52:06.4786+00:00
-- url     : https://prove2.me/submissions/409e4c21-ef3b-4d26-8198-8d245d2292f0

import Mathlib.SetTheory.Cardinal.EventuallyConst
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic.FinCases
import Definitions.Def_OrdinalStepUp_Solution
import Theorems.Thm_OrdinalStepUp_ErdosRado_exists_wo_gt
import Theorems.Thm_OrdinalStepUp_ErdosRado_nextIn_mem
import Theorems.Thm_OrdinalStepUp_ErdosRado_wo_nextIn
import Theorems.Thm_OrdinalStepUp_ErdosRado_discNext_eq

set_option autoImplicit true
open OrdinalStepUp OrdinalStepUp.ErdosRado
open Ordinal
universe u
variable {n r : ℕ} {α β κ μ θ : Ordinal} {a b c : SetOrd} {𝒜 ℬ 𝒞 : Set SetOrd}
  {V : Type u} {wo wo' : WellOrder} {x : wo.α}
namespace OrdinalStepUp.ErdosRado
theorem _root_.solution (hA : IsIndec (otp 𝒜))
    (hup : ∀ a ∈ 𝒜, ∀ b ∈ 𝒜, ∀ c ∈ 𝒜, a ≺w b → b ≺w c → disc a b < disc b c)
    (ha : a ∈ 𝒜) (hb : b ∈ 𝒜) (hab : a ≺w b) :
    discNext 𝒜 a < discNext 𝒜 b := by
  have hex : ∃ y, y ∈ 𝒜 ∧ b ≺w y := exists_wo_gt hA hb
  rw [discNext_eq hup ha hb hab, discNext]
  exact hup a ha b hb _ (nextIn_mem hex) hab (wo_nextIn hex)
end OrdinalStepUp.ErdosRado
