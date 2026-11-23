-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.muK_univ_pos
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:14:44.695578+00:00
-- url     : https://prove2.me/submissions/1e940d7e-a2c1-4d8e-918d-899dfd37dca5

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_KFactsA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_KFacts
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_compactSpace_KG

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS.S7
theorem _root_.solution (ε : Fin n → Bool) : 0 < (muK ε Set.univ).toReal := by
  haveI := compactSpace_KG ε
  unfold muK
  exact ENNReal.toReal_pos (isOpen_univ.measure_ne_zero _ Set.univ_nonempty)
    (isCompact_univ.measure_lt_top).ne
end ReciprocityTheory.ChartRestriction.DS.S7
