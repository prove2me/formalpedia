-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UsCompose.mem_steps
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:21:26.776544+00:00
-- url     : https://prove2.me/submissions/93487bd5-27ab-4539-923b-ee31ab20d649

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentComposition_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentComposition_HasDerivAtInvpow
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentComposition_Expand
import Theorems.Thm_PI_UnitaryGroupMassFormula_UsCompose_mem_step

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MvPolynomial
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UsCompose
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.U Formalism.REAL Formalism.FourierDecayAlt.P.BetaSesquilinearity
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace PI.UnitaryGroupMassFormula.UsCompose
theorem _root_.solution {k j ρ : ℕ} {w : List (Mat k (j + ρ))} {L : FS k (j + ρ)} :
    ∀ {e : SC (2 * (j + ρ) + k + 1) × List (Mat k (j + ρ))}, e ∈ steps k j ρ w L →
    ∃ e₀ ∈ L, e.2.length ≤ e₀.2.length + w.length ∧ ∀ Y ∈ e.2, Y ∈ e₀.2 ∨ Y ∈ w := by
  induction w with
  | nil => intro e he; exact ⟨e, he, by simp, fun Y hY => Or.inl hY⟩
  | cons X w ih =>
    intro e he
    have he' : e ∈ step k j ρ X (steps k j ρ w L) := he
    obtain ⟨e₁, he₁, h1⟩ := mem_step he'
    obtain ⟨e₀, he₀, hl, hY⟩ := ih he₁
    refine ⟨e₀, he₀, ?_, ?_⟩
    · rcases h1 with h1 | h1 <;> rw [h1] <;> simp only [List.length_cons] <;> omega
    · intro Y hYm
      rcases h1 with h1 | h1
      · rw [h1] at hYm
        rcases hY Y hYm with h | h
        · exact Or.inl h
        · exact Or.inr (List.mem_cons_of_mem _ h)
      · rw [h1] at hYm
        rcases List.mem_cons.1 hYm with rfl | hYm
        · exact Or.inr (by simp)
        · rcases hY Y hYm with h | h
          · exact Or.inl h
          · exact Or.inr (List.mem_cons_of_mem _ h)
end PI.UnitaryGroupMassFormula.UsCompose
