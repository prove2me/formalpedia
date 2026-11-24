-- Prove2me | solution 1 for P2M_PI_UnitaryGroupMassFormula_UsCost_permutationMatrix_eq_permMatrix__665b2f5dbc76
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T15:42:27.365635+00:00
-- url     : https://prove2.me/submissions/d625585c-39ce-48b8-aef1-08d5d3c6bb70

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
theorem _root_.solution (σ : Equiv.Perm (Fin p)) : wP σ = σ.permMatrix ℂ := by
  ext a b
  simp [wP, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]
end PI.UnitaryGroupMassFormula.UsCost
