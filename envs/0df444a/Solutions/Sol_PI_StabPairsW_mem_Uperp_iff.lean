-- Prove2me | solution 1 for PI.StabPairsW.mem_Uperp_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:39:06.772054+00:00
-- url     : https://prove2.me/submissions/eb6f6b2c-45a5-4096-9ad4-184368eeb73a

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerPairs_ConverseStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerPairs_IsUnitDetOfMemGV
import Theorems.Thm_PI_StabPairsW_Fm_conjTranspose

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
theorem _root_.solution (z z' : Fin (2 * r + k + 1) → ℂ) (γ : B.Mat k r) (v : Fin (2 * r + k + 1) → ℂ) :
    v ∈ Uperp k r z z' γ ↔ ((Fm k r z z' γ)ᴴ * Hpk k r) *ᵥ v = 0 := by
  rw [Fm_conjTranspose]
  rfl
end PI.StabPairsW
