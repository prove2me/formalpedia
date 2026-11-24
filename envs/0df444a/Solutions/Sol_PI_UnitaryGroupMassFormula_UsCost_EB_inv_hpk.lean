-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UsCost.EB_inv_hpk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:15:22.933267+00:00
-- url     : https://prove2.me/submissions/5c007945-f414-471e-9238-52b12e7d2a6a

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_LetterSize
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DirectionsInParabolic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Block3MulBlocks
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_Letters
import Theorems.Thm_PI_UnitaryGroupMassFormula_UsCost_inv_eq_hpk
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux5_EB_Hpk
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux5_EB_conjTranspose
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux5_EB_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux5_EB_mulF
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux5_entry_le_gN


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
    EB n⁻¹ (((2 * r + k + 1 : ℕ) : ℝ) ^ 2 * B.gN n) := by
  rw [inv_eq_hpk n hu]
  have h1 : EB nᴴ (B.gN n) := EB_conjTranspose fun i j => entry_le_gN n i j
  have h2 := EB_mulF (EB_mulF (EB_Hpk k r) h1) (EB_Hpk k r)
  refine h2.mono (le_of_eq ?_)
  ring
end PI.UnitaryGroupMassFormula.UsCost
