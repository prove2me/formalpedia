-- Prove2me | solution 1 for PI.StabSplit.FixW.uOf_out_col
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T15:39:26.233548+00:00
-- url     : https://prove2.me/submissions/fcc1d74e-3d3d-4afb-8441-1eb76e794fb5

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerFlagSplitting_SubFlag
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerFlagSplitting_FixSub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2 Formalism.QuantumDeterminants.GBasic
noncomputable section
open PI PI.StabSplit PI.StabSplit.FixW
namespace PI.StabSplit.FixW
theorem _root_.solution {k r : ℕ} (g : B.Mat k r) (i j : Fin (2 * r + k + 1))
    (hj : j.val < r ∨ r + k < j.val) : uOf k r g i j = if i = j then 1 else 0 := by
  simp only [uOf, of_apply]
  rw [if_neg (by omega)]
end PI.StabSplit.FixW
