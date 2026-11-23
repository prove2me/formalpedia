-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.measurable_tmUpd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:02:42.370812+00:00
-- url     : https://prove2.me/submissions/b4c6a66d-2638-40d3-aa4e-dcc15aede341

import Definitions.Def_ReciprocityTheory_SemistableReduction_SphereLogIntegrableStatement
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusMeanA
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusMeanB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open MeasureTheory Real Function
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution (i : ι) : Measurable (tmUpd i) := by
  first
  | exact measurable_update' (a := i)
  | exact measurable_pi_iff.mpr fun j => by
      by_cases h : j = i
      · subst h; simpa [tmUpd] using measurable_snd
      · simpa [tmUpd, Function.update_of_ne h] using (measurable_pi_apply j).comp measurable_fst
end ReciprocityTheory.MultiplicativeHeights
