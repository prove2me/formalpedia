-- Prove2me | solution 1 for PI.HtPlacesSumWork.addv_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:40:25.226337+00:00
-- url     : https://prove2.me/submissions/cf715cec-ff1a-4d83-89f3-58a645b9af77

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
variable {S L : Type*} [CommRing S] [IsDedekindDomain S] [Field L] [Algebra S L]
  [IsFractionRing S L] (v : HeightOneSpectrum S)
namespace PI.HtPlacesSumWork
theorem _root_.solution {x : L} (hx : x ≠ 0) :
    addv L v x = (((-log (v.valuation L x) : ℤ)) : WithTop ℤ) := by
  rw [addv, AddValuation.of_apply, if_neg hx]
end PI.HtPlacesSumWork
