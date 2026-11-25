-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.xp_term
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:46:46.794002+00:00
-- url     : https://prove2.me/submissions/e98cd077-42ff-4ce8-8424-0efa470972eb

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_CoeffRescaleExpandOfNotDvd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModEvalSer
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_CoeffIn_xp


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
theorem _root_.solution (f : PowerSeries ℂ) {k : ℕ} (hk : k ≠ 0) (x : ℂ) (m : ℕ) :
    PowerSeries.coeff (k * m) (xp k f) * x ^ (k * m) = PowerSeries.coeff m f * (x ^ k) ^ m := by
  rw [xp, PowerSeries.coeff_mk, if_pos (dvd_mul_right k m),
    Nat.mul_div_cancel_left m (Nat.pos_of_ne_zero hk), pow_mul]
end ReciprocityTheory.ChartRestriction.L1
