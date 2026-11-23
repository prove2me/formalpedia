-- Prove2me | solution 1 for PI.HwUniqW.block_mk
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:30:53.38723+00:00
-- url     : https://prove2.me/submissions/17327b91-4156-4105-a8de-80669b761294

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HighestWeightUniqueness_HpkMulMulHpkApply
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HighestWeightUniqueness_UnitaryOfBlockWMem

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
open PI PI.HwUniqW
open PI.UpqRep
variable {k r : ℕ}
namespace PI.HwUniqW
theorem _root_.solution {i : Fin (2 * r + k + 1)} (hi : InB k r i) (p : i.val - r < k) : bl k r ⟨i.val - r, p⟩ = i := by
  have hi' : r ≤ i.val ∧ i.val < r + k := hi
  apply Fin.ext
  show r + (i.val - r) = i.val
  omega
end PI.HwUniqW
