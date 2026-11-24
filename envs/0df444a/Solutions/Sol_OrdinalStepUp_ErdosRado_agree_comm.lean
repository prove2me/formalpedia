-- Prove2me | solution 1 for OrdinalStepUp.ErdosRado.agree_comm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:49:30.869603+00:00
-- url     : https://prove2.me/submissions/baeea145-63ea-431e-a60c-b44d1c9b7de9

import Mathlib.SetTheory.Cardinal.EventuallyConst
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic.FinCases
import Definitions.Def_OrdinalStepUp_Solution

set_option autoImplicit true
open OrdinalStepUp OrdinalStepUp.ErdosRado
open Ordinal
universe u
variable {n r : ℕ} {α β κ μ θ : Ordinal} {a b c : SetOrd} {𝒜 ℬ 𝒞 : Set SetOrd}
  {V : Type u} {wo wo' : WellOrder} {x : wo.α}
namespace OrdinalStepUp.ErdosRado
theorem _root_.solution : Agree a b ↔ Agree b a := by
  rcases eq_or_ne a b with rfl | hne
  · rfl
  have hw : (a ≺w b) ↔ ¬ b ≺w a :=
    ⟨asymm, fun h => (trichotomous_of WO.r a b).resolve_right (·.elim hne h)⟩
  have hl : (a ≺ b) ↔ ¬ b ≺ a :=
    ⟨asymm, fun h => (trichotomous_of LexLT a b).resolve_right (·.elim hne h)⟩
  exact (iff_congr hw hl).trans not_iff_not
end OrdinalStepUp.ErdosRado
