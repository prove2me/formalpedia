-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.LinearSubstitution.wt_isU
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:25:20.128714+00:00
-- url     : https://prove2.me/submissions/ca86498b-7941-4c9f-b5bb-6547244dd2f8

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_PowFirstVarDvdSubstitution
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_EvalOneBilinearSubstitution
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_SubstitutionSplitIrreducibleOf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open NumberField MvPolynomial
open ReciprocityTheory.ChartRestriction.G.T0.LinearSubstitution
variable {K : Type} [Field K] {D N : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.T0.LinearSubstitution
theorem _root_.solution (s : V D N →₀ ℕ) : WH.wt isU s = ∑ p, s (Sum.inl p) := by
  unfold WH.wt
  rw [Fintype.sum_sum_type]
  simp [isU]
end ReciprocityTheory.ChartRestriction.G.T0.LinearSubstitution
