-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.eisensteinFourInt_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:34:13.171339+00:00
-- url     : https://prove2.me/submissions/69b37868-9382-438f-9959-2b9f70a41fc5

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModEisInt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModDeltaInt

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
theorem _root_.solution : e4Z = 1 + PowerSeries.C (240 : ℤ) * s3Z := by
  ext n
  simp only [e4Z, s3Z, map_add, PowerSeries.coeff_mk, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_one]
  split_ifs with h
  · subst h; simp
  · ring
end ReciprocityTheory.ChartRestriction.L1
