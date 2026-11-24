-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.map_subst_ps
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:46:06.134079+00:00
-- url     : https://prove2.me/submissions/f723f939-3c59-4b07-bf69-7c832c8ac58f

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
theorem _root_.solution {a : PowerSeries K} (ha : constantCoeff a = 0) (f : PowerSeries K) :
    PowerSeries.map φ (f.subst a) = (PowerSeries.map φ f).subst (PowerSeries.map φ a) := by
  erw [PowerSeries.map_subst (HasSubst.of_constantCoeff_zero ha)]
  try rfl
end ReciprocityTheory.ChartRestriction.L1
