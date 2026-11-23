-- Prove2me | solution 1 for PI.StabBigW.hpk_col
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:43:38.411451+00:00
-- url     : https://prove2.me/submissions/fda338cd-15b0-4a90-a4ce-361229787ffc

import Definitions.Def_Formalism_PeriodIntegrals_StabBig
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LargeStabilizerInverse_GLeftInv
import Theorems.Thm_PI_StabBigW_tau_val

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
open PI PI.StabBigW
open Formalism.QuantumDeterminants Formalism.QuantumDeterminants.WeylGroupFacts
variable {k r : ℕ}
namespace PI.StabBigW
theorem _root_.solution (m q : Fin (2 * r + k + 1)) :
    Hpk k r m q = if m = tau k r q then sgn k r q else 0 := by
  have ht := tau_val (k := k) (r := r) q
  unfold Hpk sgn
  by_cases hq : q.val < r ∨ r + k < q.val
  · rw [if_pos hq] at ht
    simp only [Fin.ext_iff, ht]
    split_ifs <;> first | rfl | (exfalso; omega) | norm_num
  · rw [if_neg hq] at ht
    simp only [Fin.ext_iff, ht]
    split_ifs <;> first | rfl | (exfalso; omega) | norm_num
end PI.StabBigW
