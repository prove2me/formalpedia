-- Prove2me | solution 1 for PIQnLT.herm_liftVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:32:52.805514+00:00
-- url     : https://prove2.me/submissions/a0b5d405-db45-4637-ab0e-e8a4f66cc9d9

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelTransfer_LzConjTranspose
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelTransfer_SecondCapelliMinorLevel
import Theorems.Thm_PIQnLT_hpk_mulVec_liftVec
import Theorems.Thm_PIQnLT_dot_liftVec

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
open PIQnLT
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k i r' : ℕ}
namespace PIQnLT
theorem _root_.solution (v w : Fin (2 * r' + k + 1) → ℂ) :
    herm (Hpk k (i + r')) (liftVec k i r' v) (liftVec k i r' w) = herm (Hpk k r') v w := by
  unfold herm
  rw [hpk_mulVec_liftVec, dot_liftVec]
end PIQnLT
