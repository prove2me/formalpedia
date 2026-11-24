-- Prove2me | solution 1 for PIQnLT.lev_in
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T15:55:20.447787+00:00
-- url     : https://prove2.me/submissions/d21a16c2-3ae2-4f50-bef8-051610c7f051

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelTransfer_ExpLz
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelTransfer_LzConjTranspose

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
theorem _root_.solution (j : Fin (2 * r' + k + 1)) :
    i ≤ (levPos k i r' j).val ∧ (levPos k i r' j).val < 2 * r' + k + 1 + i := by
  have := j.isLt
  simp only [levPos]
  omega
end PIQnLT
