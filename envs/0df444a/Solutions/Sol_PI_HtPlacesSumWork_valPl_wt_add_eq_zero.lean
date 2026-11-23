-- Prove2me | solution 1 for PI.HtPlacesSumWork.valPl_wt_add_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:33:39.077739+00:00
-- url     : https://prove2.me/submissions/435bf1b5-1997-400b-a88c-e2dea1a10a06

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_TheoremA
import Definitions.Def_ReciprocityTheory_SemistableReduction_AlgAll
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GaussHeights_PlaceSumHeights_PlaceSumStatements_PlaceSumLemmas_GaussValuationSums_ValPlWtAddEqZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.HtPlacesSumWork
open IsDedekindDomain WithZero IsLocalRing ReciprocityTheory.ChartRestriction.G.T0
namespace PI.HtPlacesSumWork
theorem _root_.solution {a b : WithTop ℤ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a + b = 0) :
    a = 0 := by
  induction a using WithTop.recTopCoe with
  | top => simp at h
  | coe a =>
    induction b using WithTop.recTopCoe with
    | top => simp at h
    | coe b =>
      norm_cast at ha hb h ⊢
      omega
end PI.HtPlacesSumWork
