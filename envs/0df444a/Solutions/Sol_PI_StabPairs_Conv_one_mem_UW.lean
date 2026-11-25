-- Prove2me | solution 1 for PI.StabPairs.Conv.one_mem_UW
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:36:04.513693+00:00
-- url     : https://prove2.me/submissions/0a22fb64-9cda-4753-aa41-5d48b6ebfe06

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerPairs_HermBvecFvec
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerPairs_ConverseStepOf

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
open PI PI.StabPairs PI.StabPairs.Conv
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2 PI.StabPairsW
namespace PI.StabPairs.Conv
theorem _root_.solution (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) : (1 : B.Mat k r) ∈ UWset k r z := by
  refine ⟨?_, fun a => ⟨?_, ?_⟩, ?_⟩
  · show (1 : B.Mat k r)ᴴ * Hpk k r * 1 = Hpk k r
    simp
  all_goals simp
end PI.StabPairs.Conv
