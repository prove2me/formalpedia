-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.HW.onep_KG_ext
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:04:22.326249+00:00
-- url     : https://prove2.me/submissions/4ab5f51d-48e6-4c96-9e99-ebad733040ca

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PsiExistsStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_OneParam

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.HW
open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS.HW
theorem _root_.solution {ε : Fin n → Bool} {g h : KG ε} (hgh : toMK g = toMK h) : g = h := by
  unfold toMK at hgh
  first
    | exact Subtype.ext (Subtype.ext hgh)
    | exact Subtype.ext (Subtype.ext (Units.ext hgh))
    | (unfold toM at hgh; done)
end ReciprocityTheory.ChartRestriction.DS.HW
