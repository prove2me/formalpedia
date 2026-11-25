-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.dZ_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:25:18.913831+00:00
-- url     : https://prove2.me/submissions/dbea924b-0fd0-458b-a777-4698d3d261ef

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModEisInt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModDeltaInt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_eisenstein_cube_sub_sq_eq

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
theorem _root_.solution : PowerSeries.C (1728 : ℤ) * dZ = e4Z ^ 3 - e6Z ^ 2 := by
  ext n
  rw [PowerSeries.coeff_C_mul, dZ, PowerSeries.coeff_mk, eisenstein_cube_sub_sq_eq, PowerSeries.coeff_C_mul]
  exact Int.mul_ediv_cancel' (dvd_mul_right _ _)
end ReciprocityTheory.ChartRestriction.L1
