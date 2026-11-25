-- Prove2me | solution 1 for PI.UnitaryCorollaryDerivatives.cA_Dwl_append
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:35:15.876206+00:00
-- url     : https://prove2.me/submissions/6dc00658-bf9a-48f6-9160-ea42027c5299

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_CoreStar
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_CADwlSmooth

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
open Formalism.FourierDecayAlt.P.BetaSesquilinearity
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace PI.UnitaryCorollaryDerivatives
theorem _root_.solution (lam : Bool × B.Mat k r → ℂ) (w : List (Bool × B.Mat k r)) (x : Bool × B.Mat k r)
    (F : B.Mat k r → E) : Dwl lam (w ++ [x]) F = Dwl lam w (fun g => Dx x F g + lam x • F g) := by
  simp [Dwl, List.foldr_append]
end PI.UnitaryCorollaryDerivatives
