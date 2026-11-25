-- Prove2me | solution 1 for PI.ParahoricIdxZ.W.theta_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:04:12.188641+00:00
-- url     : https://prove2.me/submissions/6d9df579-dde2-4cf9-adf4-35bc32566a49

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ParahoricIndexCount_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ParahoricIndexCount_ThetaInjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open PI PI.ParahoricIdxZ PI.ParahoricIdxZ.W
variable {F : Type} [Field F] (O : Subring F) (ϖ : F)
namespace PI.ParahoricIdxZ.W
theorem _root_.solution {a t : ℕ} {R : Type} [CommRing R] :
    theta (1 : Matrix (Fin a) (Fin a) R) 0 0 (1 : Matrix (Fin t) (Fin t) R) = 1 := by
  simp [theta, Matrix.reindex_apply]
end PI.ParahoricIdxZ.W
