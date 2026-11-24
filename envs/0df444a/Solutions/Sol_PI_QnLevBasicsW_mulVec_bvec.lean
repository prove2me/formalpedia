-- Prove2me | solution 1 for PI.QnLevBasicsW.mulVec_bvec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:29:54.160522+00:00
-- url     : https://prove2.me/submissions/500b6535-f2b5-4a2f-9273-735a4f33cda8

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelLiftBasics_SplitInvInjective
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelLiftBasics_LevelGroupUnitaryHermitian

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
open PI PI.QnLevBasicsW
open Formalism.QuantumDeterminants
variable {k i r' : ℕ}
namespace PI.QnLevBasicsW
theorem _root_.solution {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) (q p : Fin m) : (M *ᵥ bvec q) p = M p q := by
  simp [bvec, Matrix.mulVec, dotProduct, Pi.single_apply]
end PI.QnLevBasicsW
