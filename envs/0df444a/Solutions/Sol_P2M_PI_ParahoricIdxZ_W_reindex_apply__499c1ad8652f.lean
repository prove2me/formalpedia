-- Prove2me | solution 1 for P2M_PI_ParahoricIdxZ_W_reindex_apply__499c1ad8652f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:50:04.439194+00:00
-- url     : https://prove2.me/submissions/eb85820d-d47a-4360-8fe6-0e5c827c66b0

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
theorem _root_.solution {a t : ℕ} {R : Type} (A : Matrix (Fin (a + t)) (Fin (a + t)) R)
    (x y : Fin a ⊕ Fin t) :
    Matrix.reindex finSumFinEquiv.symm finSumFinEquiv.symm A x y =
      A (finSumFinEquiv x) (finSumFinEquiv y) := by
  rfl
end PI.ParahoricIdxZ.W
