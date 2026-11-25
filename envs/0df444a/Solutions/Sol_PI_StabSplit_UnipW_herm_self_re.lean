-- Prove2me | solution 1 for PI.StabSplit.UnipW.herm_self_re
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:28:00.062995+00:00
-- url     : https://prove2.me/submissions/08e31716-0551-41c1-8e76-b113ad01a0d8

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerFlagSplitting_SubFlag
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerFlagSplitting_NilpotentOrthogonalComplement
import Theorems.Thm_PI_StabSplit_UnipW_star_dotProduct_Hpk_mulVec_eq_sum_sub

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
theorem _root_.solution {k r : ℕ} {w : Fin (2 * r + k + 1) → ℂ} (hw : perpX k r w) (hL : w (Lk k r) = 0) :
    (herm (Hpk k r) w w).re =
      ∑ i, if (r ≤ i.val ∧ i.val ≤ r + k) then Complex.normSq (w i) else 0 := by
  rw [star_dotProduct_Hpk_mulVec_eq_sum_sub hw hw, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs with h
  · by_cases hi : i.val = r + k
    · have e : i = Lk k r := Fin.ext hi
      rw [e, hL]
      simp
    · simp only [sgn, if_neg hi, one_mul]
      rw [mul_comm, Complex.star_def, Complex.mul_conj, Complex.ofReal_re]
  · simp
end PI.StabSplit.UnipW
