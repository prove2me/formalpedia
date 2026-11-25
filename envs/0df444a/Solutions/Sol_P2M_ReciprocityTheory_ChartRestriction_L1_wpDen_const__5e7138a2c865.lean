-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_L1_wpDen_const__5e7138a2c865
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:53:27.41196+00:00
-- url     : https://prove2.me/submissions/507a3c41-d2a3-4522-a2f8-df19e0178d18

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
variable {K L : Type} [Field K] [Field L] (φ : K →+* L) (g2 g3 : K)
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution {K : Type} [Field K] (g2 g3 : K) : constantCoeff (wpDen g2 g3) = 1 := by
  unfold wpDen
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_mk]
  simp
end ReciprocityTheory.ChartRestriction.L1
