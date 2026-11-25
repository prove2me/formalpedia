-- Prove2me | solution 1 for PI.UnitaryCorollaryDerivatives.sum_cost_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:35:52.319362+00:00
-- url     : https://prove2.me/submissions/fd254b8d-f30c-4d96-8b7f-3757a9058ee8

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_CoreStar
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_WeightBoundMultiplicative

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
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism.FourierDecayAlt.P.BetaSesquilinearity
namespace PI.UnitaryCorollaryDerivatives
theorem _root_.solution {k r : ℕ} (c : B.Mat k r → ℕ) {u v u₁ v₁ : List (B.Mat k r)} (hu : u₁.Sublist u)
    (hv : v₁.Sublist v) : (((u₁ ++ v₁).map c).sum : ℝ) ≤ (((u ++ v).map c).sum : ℝ) := by
  have h := ((hu.append hv).map c).sum_le_sum (fun _ _ => Nat.zero_le _)
  exact_mod_cast h
end PI.UnitaryCorollaryDerivatives
