-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.Conv.summable
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:42:19.8382+00:00
-- url     : https://prove2.me/submissions/dce75ced-32d9-4d57-97b8-70b5eb1f67db

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_CoeffRescaleExpandOfNotDvd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModEvalSer
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_Conv_summable_norm

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
namespace Conv
theorem _root_.solution {f : PowerSeries ℂ} (hf : Conv f) {x : ℂ} (hx : ‖x‖ < 1) :
    Summable fun n => PowerSeries.coeff n f * x ^ n := (hf.summable_norm hx).of_norm
end Conv
end ReciprocityTheory.ChartRestriction.L1
