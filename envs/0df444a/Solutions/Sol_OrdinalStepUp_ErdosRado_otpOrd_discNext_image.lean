-- Prove2me | solution 1 for OrdinalStepUp.ErdosRado.otpOrd_discNext_image
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:52:43.469113+00:00
-- url     : https://prove2.me/submissions/09115df5-e40b-4209-9ab3-554ed5a5ec47

import Mathlib.SetTheory.Cardinal.EventuallyConst
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic.FinCases
import Definitions.Def_OrdinalStepUp_Solution
import Theorems.Thm_OrdinalStepUp_ErdosRado_otpOf_image
import Theorems.Thm_OrdinalStepUp_ErdosRado_discNext_strictMono

set_option autoImplicit true
open OrdinalStepUp OrdinalStepUp.ErdosRado
open Ordinal
universe u
variable {n r : ℕ} {α β κ μ θ : Ordinal} {a b c : SetOrd} {𝒜 ℬ 𝒞 : Set SetOrd}
  {V : Type u} {wo wo' : WellOrder} {x : wo.α}
namespace OrdinalStepUp.ErdosRado
theorem _root_.solution (hA : IsIndec (otp 𝒜))
    (hup : ∀ a ∈ 𝒜, ∀ b ∈ 𝒜, ∀ c ∈ 𝒜, a ≺w b → b ≺w c → disc a b < disc b c) :
    otpOrd (discNext 𝒜 '' 𝒜) = otp 𝒜 :=
  otpOf_image (wo := WO) (wo' := ordWO) (f := discNext 𝒜)
    (fun _ ha _ hb hab => discNext_strictMono hA hup ha hb hab)
end OrdinalStepUp.ErdosRado
