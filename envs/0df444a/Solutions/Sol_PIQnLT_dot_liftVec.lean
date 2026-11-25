-- Prove2me | solution 1 for PIQnLT.dot_liftVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:17:04.060509+00:00
-- url     : https://prove2.me/submissions/ba0bbea2-1204-4f12-82c0-d9303123e6b3

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelTransfer_LzConjTranspose
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelTransfer_SecondCapelliMinorLevel
import Theorems.Thm_PIQnLT_liftVec_lev
import Theorems.Thm_PIQnLT_liftVec_out
import Theorems.Thm_PIQnLT_sum_lev


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
theorem _root_.solution (w u : Fin (2 * r' + k + 1) → ℂ) :
    star (liftVec k i r' w) ⬝ᵥ liftVec k i r' u = star w ⬝ᵥ u := by
  simp only [dotProduct, Pi.star_apply]
  rw [sum_lev]
  · simp only [liftVec_lev]
  · intro q hq
    rw [liftVec_out _ _ hq, star_zero, zero_mul]
end PIQnLT
