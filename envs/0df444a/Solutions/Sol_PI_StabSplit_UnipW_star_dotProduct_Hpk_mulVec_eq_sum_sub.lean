-- Prove2me | solution 1 for PI.StabSplit.UnipW.star_dotProduct_Hpk_mulVec_eq_sum_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:10:04.764386+00:00
-- url     : https://prove2.me/submissions/d1f59342-09f8-458c-94b5-1a3cde0b3fa9

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerFlagSplitting_SubFlag
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerFlagSplitting_NilpotentOrthogonalComplement
import Theorems.Thm_PI_StabSplit_UnipW_sig_gt
import Theorems.Thm_PI_StabSplit_UnipW_herm_coord

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
    herm (Hpk k r) v w =
      ∑ i, if (r ≤ i.val ∧ i.val ≤ r + k) then star (w i) * (sgn k r i * v i) else 0 := by
  rw [herm_coord]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs with h
  · have hs : sig k r i = i := by
      unfold sig
      rw [if_neg (by omega)]
    rw [hs]
  · by_cases hi : i.val < r
    · rw [hv _ (sig_gt i hi)]
      ring
    · rw [hw i (by omega)]
      simp
end PI.StabSplit.UnipW
