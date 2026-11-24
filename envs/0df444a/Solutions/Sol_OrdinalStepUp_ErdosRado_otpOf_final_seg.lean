-- Prove2me | solution 1 for OrdinalStepUp.ErdosRado.otpOf_final_seg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:50:04.5968+00:00
-- url     : https://prove2.me/submissions/2f2a5699-3f1c-4c71-a862-5c508c7e179b

import Mathlib.SetTheory.Cardinal.EventuallyConst
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic.FinCases
import Definitions.Def_OrdinalStepUp_Solution
import Theorems.Thm_OrdinalStepUp_ErdosRado_IsIndec_eq_of_add_eq_of_isPrincipal
import Theorems.Thm_OrdinalStepUp_ErdosRado_nonempty_splitIso

set_option autoImplicit true
open OrdinalStepUp OrdinalStepUp.ErdosRado
open Ordinal
universe u
variable {n r : ℕ} {α β κ μ θ : Ordinal} {a b c : SetOrd} {𝒜 ℬ 𝒞 : Set SetOrd}
  {V : Type u} {wo wo' : WellOrder} {x : wo.α}
namespace OrdinalStepUp.ErdosRado
theorem _root_.solution
    {𝒜 ℬ : Set _} (hA : IsIndec (otpOf wo 𝒜)) (hBA : ℬ ⊆ 𝒜)
    (hfinal : ∀ y ∈ ℬ, ∀ x ∈ 𝒜, wo.r y x → x ∈ ℬ)
    (hsmall : otpOf wo (𝒜 \ ℬ) < otpOf wo 𝒜) :
    otpOf wo ℬ = otpOf wo 𝒜 :=
  have : otpOf _ (𝒜 \ ℬ) + otpOf _ ℬ = otpOf _ 𝒜 := by
    rw [otpOf, otpOf, otpOf, ← type_sum_lex]
    exact type_eq.2 (nonempty_splitIso hBA hfinal)
  hA.eq_of_add_eq_of_isPrincipal hsmall this
end OrdinalStepUp.ErdosRado
