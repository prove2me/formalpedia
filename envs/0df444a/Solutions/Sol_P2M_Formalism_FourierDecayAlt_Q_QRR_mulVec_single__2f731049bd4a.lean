-- Prove2me | solution 1 for P2M_Formalism_FourierDecayAlt_Q_QRR_mulVec_single__2f731049bd4a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T15:42:31.64887+00:00
-- url     : https://prove2.me/submissions/ee8f4d3a-5974-4987-bf78-34fec3cb4a2c

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RightSingleRule_PatEntryZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RightSingleRule_EllSingleZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.QRR
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.Q.QRR
theorem _root_.solution (a b : Fin (2 * r + k + 1)) (c : ℂ) (z : Fin (2 * r + k + 1) → ℂ)
    (i : Fin (2 * r + k + 1)) : (Matrix.single a b c *ᵥ z) i = if i = a then c * z b else 0 := by
  by_cases h : i = a
  · subst h
    simp [Matrix.mulVec, dotProduct, Matrix.single_apply]
  · simp [Matrix.mulVec, dotProduct, Matrix.single_apply, h, Ne.symm h]
end Formalism.FourierDecayAlt.Q.QRR
