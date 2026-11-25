-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Sh.PTb.finsupp_prod_eq_multiset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:28:51.49796+00:00
-- url     : https://prove2.me/submissions/1a645950-d557-48bc-8524-b50f580beb2f

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
theorem _root_.solution {S ι : Type*} [CommMonoid S] (x : ι → S) (e : ι →₀ ℕ) :
    e.prod (fun i m => x i ^ m) = (e.toMultiset.map x).prod := by
  first
  | (rw [← Finsupp.toMultiset_map, Finsupp.prod_toMultiset,
      Finsupp.prod_mapDomain_index (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)])
  | (induction e using Finsupp.induction with
      | zero => simp
      | single_add i m f hi hm ih =>
        rw [Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _), ih]
        simp [Finsupp.toMultiset_single, Multiset.map_nsmul, Multiset.prod_nsmul])
end ReciprocityTheory.ChartRestriction.G.Sh.PTb
