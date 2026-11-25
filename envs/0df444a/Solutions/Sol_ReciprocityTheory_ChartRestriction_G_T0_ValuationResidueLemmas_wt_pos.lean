-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.ValuationResidueLemmas.wt_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:30:13.25543+00:00
-- url     : https://prove2.me/submissions/cd1d1ab6-6c00-44ae-885e-03fc3f32210b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HtDefs
import Definitions.Def_ReciprocityTheory_SemistableReduction_AlgAll
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_IsUnitOfValEqZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G.T0.ValuationResidueLemmas
namespace ReciprocityTheory.ChartRestriction.G.T0.ValuationResidueLemmas
theorem _root_.solution {a b : WithTop ℤ} (ha : 0 ≤ a) (hb : 0 < b) : 0 < a + b := by
  calc (0 : WithTop ℤ) < b := hb
    _ = 0 + b := (zero_add b).symm
    _ ≤ a + b := by
      first
        | exact add_le_add_right ha b
        | exact add_le_add_left ha b
        | gcongr
end ReciprocityTheory.ChartRestriction.G.T0.ValuationResidueLemmas
