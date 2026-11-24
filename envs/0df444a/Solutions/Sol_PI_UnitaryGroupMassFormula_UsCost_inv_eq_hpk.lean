-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UsCost.inv_eq_hpk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T15:54:53.970505+00:00
-- url     : https://prove2.me/submissions/b3cec121-8041-4051-9fb6-961c2e4b2c53

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_LetterSize
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DirectionsInParabolic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Block3MulBlocks
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_Letters
import Theorems.Thm_Formalism_QuantumDeterminants_GBasic_Hpk_sq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.Ux5
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UsCost
namespace PI.UnitaryGroupMassFormula.UsCost
theorem _root_.solution {k r : ℕ} (n : B.Mat k r) (hu : nᴴ * Hpk k r * n = Hpk k r) :
    n⁻¹ = Hpk k r * nᴴ * Hpk k r := by
  apply Matrix.inv_eq_left_inv
  rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc nᴴ, hu, Formalism.QuantumDeterminants.GBasic.Hpk_sq]
end PI.UnitaryGroupMassFormula.UsCost
