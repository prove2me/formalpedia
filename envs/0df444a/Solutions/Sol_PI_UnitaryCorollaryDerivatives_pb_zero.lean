-- Prove2me | solution 1 for PI.UnitaryCorollaryDerivatives.pb_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:35:44.957416+00:00
-- url     : https://prove2.me/submissions/69337489-ef0b-49fb-a2f2-717b0308f509

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
section
open Matrix
open scoped ComplexConjugate
noncomputable section
namespace PI.UnitaryCorollaryDerivatives
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.FourierDecayAlt.P.BetaSesquilinearity
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
section pb
variable {k r : ℕ}
private theorem Dw_const_zero (w : List (Bool × B.Mat k r)) :
    Dw w (fun _ : B.Mat k r => (0 : ℂ)) = fun _ => 0 := by
  induction w with
  | nil => rfl
  | cons x w ih =>
    have h' : List.foldr Dx (fun _ : B.Mat k r => (0 : ℂ)) w = fun _ => 0 := ih
    simp only [Dw, List.foldr, Dx, h']
    split_ifs <;> funext g <;> simp [B.LdV, RdV]
end pb
end PI.UnitaryCorollaryDerivatives
end
end

set_option autoImplicit false
open Matrix
open scoped ComplexConjugate
noncomputable section
open PI PI.UnitaryCorollaryDerivatives
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.FourierDecayAlt.P.BetaSesquilinearity
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
namespace PI.UnitaryCorollaryDerivatives
theorem _root_.solution (e : ℝ) : PG e (fun _ : B.Mat k r => (0 : ℂ)) := by
  unfold PG
  refine ⟨contDiff_const, fun n => ⟨0, fun w _ _ g _ => ?_⟩⟩
  rw [Dw_const_zero]
  simp
end PI.UnitaryCorollaryDerivatives
