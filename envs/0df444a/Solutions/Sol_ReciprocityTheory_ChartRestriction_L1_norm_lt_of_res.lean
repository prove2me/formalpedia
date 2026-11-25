-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.norm_lt_of_res
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:38:45.162079+00:00
-- url     : https://prove2.me/submissions/4aedd629-c4b0-4cad-8add-00e403c55dbc

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModGDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModGBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModLocD

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical UpperHalfPlane Pointwise
open NumberField IsDedekindDomain Formalism.L2.Th1.CM Neutral.HilbertClassField
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution {l : ℕ} [Fact l.Prime] {r : PadicAlgCl l → PadicAlgCl l}
    (hr : ∀ z : PadicAlgCl l, ‖z‖ ≤ 1 → ‖r z - z‖ < 1) {z : PadicAlgCl l} (hz : ‖z‖ < 1) : ‖r z‖ < 1 := by
  have h := PadicAlgCl.isNonarchimedean l (r z - z) z
  rw [sub_add_cancel] at h
  exact lt_of_le_of_lt h (max_lt (hr z hz.le) hz)
end ReciprocityTheory.ChartRestriction.L1
