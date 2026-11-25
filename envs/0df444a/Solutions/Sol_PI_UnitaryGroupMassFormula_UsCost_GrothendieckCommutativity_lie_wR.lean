-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UsCost.GrothendieckCommutativity.lie_wR
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:07:02.953004+00:00
-- url     : https://prove2.me/submissions/c70260ca-1f5b-4878-9248-7be70ac873da

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_LetterSize
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_RightRegularActionListDLREqAppend

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.BetaSesquilinearity
open scoped ContDiff
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UsCost PI.UnitaryGroupMassFormula.UsCost.GrothendieckCommutativity
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
attribute [local instance] PI.UnitaryGroupMassFormula.UsCost.GrothendieckCommutativity.clmNACG
attribute [local instance] PI.UnitaryGroupMassFormula.UsCost.GrothendieckCommutativity.clmNS
namespace PI.UnitaryGroupMassFormula.UsCost.GrothendieckCommutativity
theorem _root_.solution {v : List (B.Mat k r)} (hv : ∀ X ∈ v, B.inLie k r X) : ∀ x ∈ wR v, B.inLie k r x.2 := by
  intro x hx
  simp only [wR, List.mem_map] at hx
  obtain ⟨X, hX, rfl⟩ := hx
  exact hv X hX
end PI.UnitaryGroupMassFormula.UsCost.GrothendieckCommutativity
