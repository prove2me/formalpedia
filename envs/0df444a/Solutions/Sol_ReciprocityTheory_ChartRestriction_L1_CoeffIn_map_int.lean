-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.CoeffIn.map_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:37:19.38157+00:00
-- url     : https://prove2.me/submissions/023dda8d-fa75-4291-8587-690e9d0d0972

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_CoeffRescaleExpandOfNotDvd

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
namespace CoeffIn
theorem _root_.solution (R : Subring ℂ) (f : PowerSeries ℤ) : CoeffIn R (f.map (Int.castRingHom ℂ)) := by
  intro n
  rw [PowerSeries.coeff_map, eq_intCast]
  exact intCast_mem R _
end CoeffIn
end ReciprocityTheory.ChartRestriction.L1
