-- Prove2me | solution 1 for PI.FrameInd.indep_of_det
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:01:22.965963+00:00
-- url     : https://prove2.me/submissions/953f7677-c3c1-43dd-b3a4-d3b9bed88507

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FrameInduction_NegBound
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FrameInduction_FinrankUperpOfDet
import Theorems.Thm_PI_FrameInd_Vc_mulVec
import Theorems.Thm_PI_FrameInd_Vc_inj

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
theorem _root_.solution (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (g : B.Mat k r)
    (hdet : (gramM k r z z' g).det ≠ 0) : LinearIndependent ℂ (gramVec k r z z' g) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  have h1 : Vc k r z z' g *ᵥ c = 0 := by rw [Vc_mulVec]; exact hc
  exact congrFun (Vc_inj k r z z' g hdet c h1) i
end PI.FrameInd
