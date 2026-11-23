-- Prove2me | solution 1 for PI.HtPlacesSumWork.addv_alg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:42:37.643033+00:00
-- url     : https://prove2.me/submissions/75e7cd23-9402-4a80-a002-1a6036e05b09

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_TheoremA
import Definitions.Def_ReciprocityTheory_SemistableReduction_AlgAll
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GaussHeights_PlaceSumHeights_PlaceSumStatements_PlaceSumLemmas_GaussValuationSums_ValPlWtAddEqZero
import Theorems.Thm_PI_HtPlacesSumWork_addv_apply

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
variable {S L : Type*} [CommRing S] [IsDedekindDomain S] [Field L] [Algebra S L]
  [IsFractionRing S L] (v : HeightOneSpectrum S)
namespace PI.HtPlacesSumWork
theorem _root_.solution {s : S} (hs : s ≠ 0) :
    addv L v (algebraMap S L s) = (((-log (v.intValuation s) : ℤ)) : WithTop ℤ) := by
  rw [addv_apply v ((map_ne_zero_iff _ (IsFractionRing.injective S L)).2 hs),
    HeightOneSpectrum.valuation_of_algebraMap]
end PI.HtPlacesSumWork
