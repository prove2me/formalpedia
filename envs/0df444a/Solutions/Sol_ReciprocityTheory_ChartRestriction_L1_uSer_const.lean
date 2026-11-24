-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.uSer_const
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:46:10.38412+00:00
-- url     : https://prove2.me/submissions/2df36c4a-1a3e-40a3-b222-c6f083dddefb

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_CoeffOneSubstOfConstantCoeffEqZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM
variable {K : Type} [Field K] (g2 g3 : K)
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution : constantCoeff (uSer g2 g3) = 0 := by
  unfold uSer
  rw [map_mul, map_mul, constantCoeff_X, zero_mul, zero_mul]
end ReciprocityTheory.ChartRestriction.L1
