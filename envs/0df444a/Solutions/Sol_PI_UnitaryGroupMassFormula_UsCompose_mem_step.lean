-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UsCompose.mem_step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:10:33.304365+00:00
-- url     : https://prove2.me/submissions/e5887071-577a-44ea-a134-c7791dccfffe

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentComposition_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentComposition_HasDerivAtInvpow
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentComposition_Expand

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
theorem _root_.solution {k j ρ : ℕ} {X : Mat k (j + ρ)} {L : FS k (j + ρ)}
    {e : SC (2 * (j + ρ) + k + 1) × List (Mat k (j + ρ))} (he : e ∈ step k j ρ X L) :
    ∃ e₀ ∈ L, e.2 = e₀.2 ∨ e.2 = X :: e₀.2 := by
  rw [step, List.mem_flatMap] at he
  obtain ⟨e₀, he₀, h⟩ := he
  refine ⟨e₀, he₀, ?_⟩
  simp only [stepOne, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl <;> simp
end PI.UnitaryGroupMassFormula.UsCompose
