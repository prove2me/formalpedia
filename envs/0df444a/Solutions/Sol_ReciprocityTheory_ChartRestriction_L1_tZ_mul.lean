-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.tZ_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:56:51.750714+00:00
-- url     : https://prove2.me/submissions/938dfb08-4d3c-403b-ac37-faefbe62c49a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModEisInt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModDeltaInt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_sigma_congr

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
theorem _root_.solution : PowerSeries.C (12 : ℤ) * tZ =
    PowerSeries.C (5 : ℤ) * s3Z + PowerSeries.C (7 : ℤ) * s5Z := by
  ext n
  simp only [map_add, PowerSeries.coeff_C_mul, tZ, s3Z, s5Z, PowerSeries.coeff_mk]
  exact Int.mul_ediv_cancel' (sigma_congr n)
end ReciprocityTheory.ChartRestriction.L1
