-- Prove2me | solution 1 for P2M_PI_UnitaryGroupMassFormula_UsCost_rn_mem__52f76f729929
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:25:26.813074+00:00
-- url     : https://prove2.me/submissions/976f9d4a-732c-4409-967c-d1eeed75d423

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_LetterSize
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_Smooth

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.REAL
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UsCost
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {n : WithTop ℕ∞} {x₀ : X}
variable {k p s ρ : ℕ} {σ : Equiv.Perm (Fin p)} {d : Fin p → ℂ}
namespace PI.UnitaryGroupMassFormula.UsCost
theorem _root_.solution (hRP : RadicalParam) (j : ℕ) (x : RC k j ρ) : Rn k j ρ x ∈ B.GV k (j + ρ) := by
  have hr : Rn k j ρ x ∈ Rset k j ρ := (hRP k j ρ).2.1 ▸ Set.mem_range_self x
  exact ((hRP k j ρ).2.2 hr).1
end PI.UnitaryGroupMassFormula.UsCost
