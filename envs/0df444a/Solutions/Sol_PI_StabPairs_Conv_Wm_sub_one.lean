-- Prove2me | solution 1 for PI.StabPairs.Conv.Wm_sub_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:34:19.137552+00:00
-- url     : https://prove2.me/submissions/0349d8ce-118b-4903-a190-fe8dca69ce7f

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerPairs_IsUnitDetOfMemGV
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerPairs_UtSubOneLast
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerPairs_HermBvecFvec

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
open PI PI.StabPairs PI.StabPairs.Conv
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2 PI.StabPairsW
namespace PI.StabPairs.Conv
theorem _root_.solution {r : ℕ} (u u' : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) :
    Wm u u' - 1 = Matrix.fromBlocks (u - 1) 0 0 (u' - 1) := by
  unfold Wm
  ext (i | i) (j | j) <;> simp [Matrix.one_apply]
end PI.StabPairs.Conv
