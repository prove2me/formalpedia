-- Prove2me | solution 1 for PI.StabBigW.dd_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:26:14.812305+00:00
-- url     : https://prove2.me/submissions/e7946e08-0058-4de9-ab8d-2156defcb969

import Definitions.Def_Formalism_PeriodIntegrals_StabBig
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LargeStabilizerInverse_GLeftInv

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
theorem _root_.solution {c : Fin r → ℂ} (hc : ∀ a, c a ≠ 0) (j : Fin (2 * r + k + 1))
    (hj : j.val < r ∨ r + k < j.val) : dd k r c j ≠ 0 := by
  unfold dd
  split_ifs with h1 h2
  · exact hc _
  · exact inv_ne_zero (star_ne_zero.mpr (hc _))
  · exfalso
    omega
end PI.StabBigW
