-- Prove2me | solution 1 for PI.UnitaryCorollaryDerivatives.cB_unitLie
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T15:52:45.895019+00:00
-- url     : https://prove2.me/submissions/8c644c09-5cce-4976-bd26-d5bdc8ad9520

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_CADwlSmooth
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_CBLamnorm

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
namespace PI.UnitaryCorollaryDerivatives
theorem _root_.solution {k j ρ : ℕ} {u : List (B.Mat k (j + ρ))} (hu : unitP k j ρ u) :
    ∀ X ∈ u, B.unitLie k (j + ρ) X := fun X hX => ⟨(hu X hX).1.1, (hu X hX).2⟩
end PI.UnitaryCorollaryDerivatives
