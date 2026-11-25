-- Prove2me | solution 1 for PI.StabPairsW.inv_mem_GV
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:41:55.838459+00:00
-- url     : https://prove2.me/submissions/61a9417c-089a-44e1-b585-bc13f2bc6312

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerPairs_ConverseStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerPairs_IsUnitDetOfMemGV
import Theorems.Thm_PI_StabPairsW_mem_GV_iff
import Theorems.Thm_PI_StabPairsW_isUnit_det_of_mem_GV

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open PI PI.StabPairsW
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2
variable {k r : ℕ}
namespace PI.StabPairsW
theorem _root_.solution {g : B.Mat k r} (hg : g ∈ B.GV k r) : g⁻¹ ∈ B.GV k r := by
  have hu := isUnit_det_of_mem_GV hg
  rw [mem_GV_iff] at *
  calc (g⁻¹)ᴴ * Hpk k r * g⁻¹ = (g⁻¹)ᴴ * (gᴴ * Hpk k r * g) * g⁻¹ := by rw [hg]
    _ = (g * g⁻¹)ᴴ * Hpk k r * (g * g⁻¹) := by
        rw [Matrix.conjTranspose_mul]
        simp only [Matrix.mul_assoc]
    _ = Hpk k r := by
        rw [Matrix.mul_nonsing_inv _ hu]
        simp
end PI.StabPairsW
