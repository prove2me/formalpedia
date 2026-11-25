-- Prove2me | solution 1 for PI.FrameInd.det_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:40:50.76996+00:00
-- url     : https://prove2.me/submissions/2acc6e10-bc03-4bdd-989b-a38f9d4f79f0

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FrameInduction_NegBound
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FrameInduction_FinrankUperpOfDet
import Theorems.Thm_Formalism_QuantumDeterminants_group_gram_holds


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
theorem _root_.solution (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : B.Mat k r) (hs : Std k r z z')
    (hp : PosPt k r z z' γ) : (gramM k r z z' γ).det ≠ 0 := by
  intro h0
  have h := Formalism.QuantumDeterminants.group_gram_holds k r z z' hs.2.1.1 hs.2.2.1 γ hp.1
  rw [h0, mul_zero] at h
  have : Gf k r z z' γ = 0 := by exact_mod_cast h
  linarith [hp.2]
end PI.FrameInd
