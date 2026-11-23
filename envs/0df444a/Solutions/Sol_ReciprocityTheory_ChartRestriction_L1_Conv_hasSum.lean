-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.Conv.hasSum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:44:50.656966+00:00
-- url     : https://prove2.me/submissions/43ce02d4-1419-462b-b74f-be5d87ca1922

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_CoeffRescaleExpandOfNotDvd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModEvalSer
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_Conv_summable

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
    HasSum (fun n => PowerSeries.coeff n f * x ^ n) (ev f x) := (hf.summable hx).hasSum
end Conv
end ReciprocityTheory.ChartRestriction.L1
