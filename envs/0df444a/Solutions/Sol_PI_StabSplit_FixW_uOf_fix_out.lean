-- Prove2me | solution 1 for PI.StabSplit.FixW.uOf_fix_out
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:27:40.952068+00:00
-- url     : https://prove2.me/submissions/66a4636c-8e68-4359-af5c-848975d59982

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerFlagSplitting_SubFlag
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerFlagSplitting_FixSub
import Theorems.Thm_PI_StabSplit_FixW_uOf_out_col
import Theorems.Thm_PI_StabSplit_FixW_mulVec_bvec

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
theorem _root_.solution {k r : ℕ} (g : B.Mat k r) (c : Fin (2 * r + k + 1))
    (hc : c.val < r ∨ r + k < c.val) : uOf k r g *ᵥ bvec c = bvec c := by
  rw [mulVec_bvec]; ext i
  rw [uOf_out_col g i c hc]; simp [bvec, Pi.single_apply]
end PI.StabSplit.FixW
