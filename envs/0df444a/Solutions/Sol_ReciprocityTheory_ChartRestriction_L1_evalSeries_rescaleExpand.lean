-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.evalSeries_rescaleExpand
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:03:18.675461+00:00
-- url     : https://prove2.me/submissions/a34bac4d-0de9-4862-96ba-5302e89adecc

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_CoeffRescaleExpandOfNotDvd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModEvalSer
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_ev_xp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_CoeffIn_sub1


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane Formalism.L2.Th1.CM
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution (f : PowerSeries ℂ) (c : ℂ) {k : ℕ} (hk : k ≠ 0) (x : ℂ) :
    ev (sub1 c k f) x = ev f (c * x ^ k) := by
  rw [sub1, ev_xp _ hk]
  unfold ev
  exact tsum_congr fun n => by rw [PowerSeries.coeff_rescale, mul_pow]; ring
end ReciprocityTheory.ChartRestriction.L1
