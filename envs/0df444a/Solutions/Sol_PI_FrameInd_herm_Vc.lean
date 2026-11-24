-- Prove2me | solution 1 for PI.FrameInd.herm_Vc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:03:19.782854+00:00
-- url     : https://prove2.me/submissions/6e1beea1-6f78-47da-bc4c-73d2765de0d3

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FrameInduction_NegBound
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FrameInduction_FinrankUperpOfDet
import Theorems.Thm_PI_FrameInd_herm_mulVec_mulVec
import Theorems.Thm_PI_FrameInd_gramM_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2
noncomputable section
open PI PI.FrameInd
namespace PI.FrameInd
theorem _root_.solution (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (g : B.Mat k r) (c d : Fin (r + 1) ⊕ Fin (r + 1) → ℂ) :
    herm (Hpk k r) (Vc k r z z' g *ᵥ c) (Vc k r z z' g *ᵥ d) = herm (gramM k r z z' g) c d := by
  rw [herm_mulVec_mulVec, ← gramM_eq]
end PI.FrameInd
