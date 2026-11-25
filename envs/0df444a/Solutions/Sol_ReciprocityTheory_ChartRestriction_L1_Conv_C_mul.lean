-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.Conv.C_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:32:55.67182+00:00
-- url     : https://prove2.me/submissions/84e2bf50-1aa3-4409-901b-839b7dc4768c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_CoeffRescaleExpandOfNotDvd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModEvalSer

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
theorem _root_.solution {f : PowerSeries ℂ} (hf : Conv f) (c : ℂ) : Conv (PowerSeries.C c * f) := by
  intro x hx
  refine ((hf x hx).mul_left ‖c‖).congr fun n => ?_
  rw [PowerSeries.coeff_C_mul, norm_mul]
  ring
end Conv
end ReciprocityTheory.ChartRestriction.L1
