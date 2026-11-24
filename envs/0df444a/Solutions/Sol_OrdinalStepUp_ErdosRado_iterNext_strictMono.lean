-- Prove2me | solution 1 for OrdinalStepUp.ErdosRado.iterNext_strictMono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:52:57.076093+00:00
-- url     : https://prove2.me/submissions/181708a4-53a6-4dd0-ad78-c46321eec79c

import Mathlib.SetTheory.Cardinal.EventuallyConst
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic.FinCases
import Definitions.Def_OrdinalStepUp_Solution
import Theorems.Thm_OrdinalStepUp_ErdosRado_iterNext_lt_succ

set_option autoImplicit true
open OrdinalStepUp OrdinalStepUp.ErdosRado
open Ordinal
universe u
variable {n r : ℕ} {α β κ μ θ : Ordinal} {a b c : SetOrd} {𝒜 ℬ 𝒞 : Set SetOrd}
  {V : Type u} {wo wo' : WellOrder} {x : wo.α}
namespace OrdinalStepUp.ErdosRado
theorem _root_.solution {𝒜 : Set SetOrd} {x : SetOrd} (hA : IsIndec (otp 𝒜))
    (hx : x ∈ 𝒜) {j k : ℕ} (hjk : j < k) :
    iterNext 𝒜 x j ≺w iterNext 𝒜 x k := by
  induction k with
  | zero => omega
  | succ k ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 hjk with h | rfl
    · exact _root_.trans (ih h) (iterNext_lt_succ hA hx k)
    · exact iterNext_lt_succ hA hx j
end OrdinalStepUp.ErdosRado
