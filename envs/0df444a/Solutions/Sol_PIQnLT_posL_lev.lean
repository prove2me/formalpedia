-- Prove2me | solution 1 for PIQnLT.posL_lev
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:32:46.948577+00:00
-- url     : https://prove2.me/submissions/550995b7-b017-47fb-9070-49d33b8e4f27

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelTransfer_LzConjTranspose
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelTransfer_SecondCapelliMinorLevel
import Theorems.Thm_PIQnLT_lev_val


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
theorem _root_.solution (k i r' : ℕ) (j : Fin (mdim k (i + r') ⟨i, by omega⟩)) :
    posL k (i + r') ⟨i, by omega⟩ j = levPos k i r' (posL k r' 0 (Fin.cast (mdim_lev k i r') j)) := by
  apply Fin.ext
  simp only [posL, lev_val, Fin.coe_cast, Fin.val_zero, Fin.val_mk]
  omega
end PIQnLT
