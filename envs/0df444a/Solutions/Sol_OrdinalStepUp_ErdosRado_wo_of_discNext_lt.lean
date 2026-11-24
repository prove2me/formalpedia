-- Prove2me | solution 1 for OrdinalStepUp.ErdosRado.wo_of_discNext_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:52:43.043194+00:00
-- url     : https://prove2.me/submissions/29879890-4811-446b-a78c-8214b644e606

import Mathlib.SetTheory.Cardinal.EventuallyConst
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic.FinCases
import Definitions.Def_OrdinalStepUp_Solution
import Theorems.Thm_OrdinalStepUp_ErdosRado_discNext_strictMono

set_option autoImplicit true
open OrdinalStepUp OrdinalStepUp.ErdosRado
open Ordinal
universe u
variable {n r : ℕ} {α β κ μ θ : Ordinal} {a b c : SetOrd} {𝒜 ℬ 𝒞 : Set SetOrd}
  {V : Type u} {wo wo' : WellOrder} {x : wo.α}
namespace OrdinalStepUp.ErdosRado
theorem _root_.solution (hA : IsIndec (otp 𝒜))
    (hup : ∀ a ∈ 𝒜, ∀ b ∈ 𝒜, ∀ c ∈ 𝒜, a ≺w b → b ≺w c → disc a b < disc b c)
    (ha : a ∈ 𝒜) (hb : b ∈ 𝒜) (h : discNext 𝒜 a < discNext 𝒜 b) :
    a ≺w b :=
  (trichotomous_of WO.r a b).resolve_right fun hr => hr.elim
    (fun e => absurd (e ▸ h) (irrefl _))
    (fun hba => absurd (discNext_strictMono hA hup hb ha hba) (asymm h))
end OrdinalStepUp.ErdosRado
