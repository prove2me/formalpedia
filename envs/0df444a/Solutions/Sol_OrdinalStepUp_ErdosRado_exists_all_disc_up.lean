-- Prove2me | solution 1 for OrdinalStepUp.ErdosRado.exists_all_disc_up
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:53:07.047697+00:00
-- url     : https://prove2.me/submissions/e465b5a2-8947-49a4-bb1b-a1f37af7bfb6

import Mathlib.SetTheory.Cardinal.EventuallyConst
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic.FinCases
import Definitions.Def_OrdinalStepUp_Solution
import Theorems.Thm_OrdinalStepUp_ErdosRado_disc_ne_of_homogeneous
import Theorems.Thm_OrdinalStepUp_ErdosRado_exists_all_up

set_option autoImplicit true
open OrdinalStepUp OrdinalStepUp.ErdosRado
open Ordinal
universe u
variable {n r : ℕ} {α β κ μ θ : Ordinal} {a b c : SetOrd} {𝒜 ℬ 𝒞 : Set SetOrd}
  {V : Type u} {wo wo' : WellOrder} {x : wo.α}
namespace OrdinalStepUp.ErdosRado
theorem _root_.solution (hA : IsIndec (otp 𝒜)) (hom : HomAgree 𝒜)
    (h : (∀ a ∈ 𝒜, ∀ b ∈ 𝒜, ∀ c ∈ 𝒜, ∀ e ∈ 𝒜, a ≺w b → b ≺w c → c ≺w e →
            disc a b < disc b c → disc b c < disc c e) ∨
         (∀ a ∈ 𝒜, ∀ b ∈ 𝒜, ∀ c ∈ 𝒜, ∀ e ∈ 𝒜, a ≺w b → b ≺w c → c ≺w e →
            disc b c < disc a b → disc c e < disc b c)) :
    ∃ ℬ ⊆ 𝒜, otp ℬ = otp 𝒜 ∧
      ∀ a ∈ ℬ, ∀ b ∈ ℬ, ∀ c ∈ ℬ, a ≺w b → b ≺w c → disc a b < disc b c :=
  exists_all_up disc hA
    (fun _ ha _ hb _ hc hab hbc => disc_ne_of_homogeneous hom ha hb hc hab hbc) h
end OrdinalStepUp.ErdosRado
