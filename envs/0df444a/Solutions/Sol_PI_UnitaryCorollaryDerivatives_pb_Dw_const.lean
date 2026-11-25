-- Prove2me | solution 1 for PI.UnitaryCorollaryDerivatives.pb_Dw_const
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:36:23.472007+00:00
-- url     : https://prove2.me/submissions/a0b815ed-d5a9-41b7-99a4-2f8efb8f4291

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_CoreStar
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_PolyBA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ComplexConjugate
noncomputable section
open PI PI.UnitaryCorollaryDerivatives
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.FourierDecayAlt.P.BetaSesquilinearity
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
namespace PI.UnitaryCorollaryDerivatives
theorem _root_.solution (c : ℂ) (w : List (Bool × B.Mat k r)) :
    ∃ c' : ℂ, ‖c'‖ ≤ ‖c‖ ∧ Dw w (fun _ => c) = fun _ => c' := by
  induction w with
  | nil => exact ⟨c, le_rfl, rfl⟩
  | cons x w ih =>
    obtain ⟨c', -, h⟩ := ih
    refine ⟨0, by simp, ?_⟩
    have h' : List.foldr Dx (fun _ => c) w = fun _ => c' := h
    simp only [Dw, List.foldr, Dx, h']
    split_ifs <;> funext g <;> simp [B.LdV, RdV]
end PI.UnitaryCorollaryDerivatives
