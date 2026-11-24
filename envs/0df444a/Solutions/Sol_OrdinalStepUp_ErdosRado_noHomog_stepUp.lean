-- Prove2me | solution 1 for OrdinalStepUp.ErdosRado.noHomog_stepUp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:55:51.20388+00:00
-- url     : https://prove2.me/submissions/6f353c30-3ad8-4117-ad7d-caef489296d0

import Mathlib.SetTheory.Cardinal.EventuallyConst
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic.FinCases
import Definitions.Def_OrdinalStepUp_Solution
import Theorems.Thm_OrdinalStepUp_ErdosRado_stepUp_noHomog

set_option autoImplicit true
open OrdinalStepUp OrdinalStepUp.ErdosRado
open Ordinal
universe u
variable {n r : ℕ} {α β κ μ θ : Ordinal} {a b c : SetOrd} {𝒜 ℬ 𝒞 : Set SetOrd}
  {V : Type u} {wo wo' : WellOrder} {x : wo.α}
namespace OrdinalStepUp.ErdosRado
theorem _root_.solution {μ α : Ordinal} (hα : 0 < α) (hμ : 1 < μ)
    (h : ∃ g : Finset Ordinal → Set.Iio μ, NoHomogOrd κ g (r + 3) (ω^α)) :
    ∃ f : Finset (Set Ordinal) → Set.Iio μ, NoHomog κ f (r + 4) (ω^α) := by
  obtain ⟨g, hg⟩ := h
  have hθ : IsIndec (ω ^ α) :=
    ⟨isPrincipal_add_omega0_opow α, one_lt_opow.2 ⟨one_lt_omega0, hα.ne'⟩⟩
  exact ⟨stepUpColour hμ g, stepUp_noHomog hμ hθ hg⟩
end OrdinalStepUp.ErdosRado
