-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Sh.PTb.card_toMultiset_eq_degree
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:03:50.599925+00:00
-- url     : https://prove2.me/submissions/c1cddafc-c656-4b7c-878c-c655975007a9

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_TangentEqLcZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_CardToMultisetEqDegree

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Sh ReciprocityTheory.ChartRestriction.G.Sh.PTb
open MvPowerSeries ReciprocityTheory.PGsh
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.Sh.PTb
theorem _root_.solution {ι : Type*} (e : ι →₀ ℕ) :
    Multiset.card e.toMultiset = e.degree := by
  first
  | (rw [Finsupp.card_toMultiset]; rfl)
  | simp [Finsupp.card_toMultiset, Finsupp.degree, Finsupp.sum]
end ReciprocityTheory.ChartRestriction.G.Sh.PTb
