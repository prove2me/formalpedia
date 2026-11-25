-- Prove2me | solution 1 for PI.StabSplit.UnipW.herm_conjW
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:38:11.118524+00:00
-- url     : https://prove2.me/submissions/389ddeac-45dd-4d33-a885-eef0ed71c3cb

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerFlagSplitting_SubFlag
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerFlagSplitting_NilpotentOrthogonalComplement
import Theorems.Thm_PI_StabSplit_UnipW_star_dotProduct_Hpk_mulVec_eq_sum_sub
import Theorems.Thm_PI_StabSplit_UnipW_star_sgn

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
open PI PI.StabSplit PI.StabSplit.UnipW
namespace PI.StabSplit.UnipW
theorem _root_.solution {k r : ℕ} {v w : Fin (2 * r + k + 1) → ℂ} (hv : perpX k r v) (hw : perpX k r w) :
    herm (Hpk k r) w v = star (herm (Hpk k r) v w) := by
  rw [star_dotProduct_Hpk_mulVec_eq_sum_sub hw hv, star_dotProduct_Hpk_mulVec_eq_sum_sub hv hw, star_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs
  · simp only [star_mul', star_star, star_sgn]
    ring
  · simp
end PI.StabSplit.UnipW
