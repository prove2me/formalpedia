-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UsCost.one_le_gN_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:49:01.391698+00:00
-- url     : https://prove2.me/submissions/b80667e1-2e10-48ad-929e-9c9f9bee1af3

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_LetterSize
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DirectionsInParabolic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Block3MulBlocks
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_Letters
import Theorems.Thm_PI_UnitaryGroupMassFormula_UsCost_inv_eq_hpk
import Theorems.Thm_PI_UnitaryGroupMassFormula_UsCost_EB_inv_hpk
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux5_EB_mulF
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux5_entry_le_gN
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
    1 ≤ ((2 * r + k + 1 : ℕ) : ℝ) ^ 3 * B.gN n ^ 2 := by
  have hinv : n⁻¹ * n = 1 := by
    rw [inv_eq_hpk n hu, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc nᴴ, hu, Formalism.QuantumDeterminants.GBasic.Hpk_sq]
  have h := EB_mulF (EB_inv_hpk n hu) (fun i j => entry_le_gN n i j)
  have i0 : Fin (2 * r + k + 1) := ⟨0, by omega⟩
  have := h i0 i0
  rw [hinv, Matrix.one_apply_eq, norm_one] at this
  refine this.trans (le_of_eq ?_)
  ring
end PI.UnitaryGroupMassFormula.UsCost
