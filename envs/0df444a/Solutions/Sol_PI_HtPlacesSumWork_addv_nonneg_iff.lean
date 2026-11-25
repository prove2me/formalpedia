-- Prove2me | solution 1 for PI.HtPlacesSumWork.addv_nonneg_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:58:29.036294+00:00
-- url     : https://prove2.me/submissions/13eabd6e-ae3c-4e1f-bb81-856222b057b7

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_TheoremA
import Definitions.Def_ReciprocityTheory_SemistableReduction_AlgAll
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GaussHeights_PlaceSumHeights_PlaceSumStatements_PlaceSumLemmas_GaussValuationSums_ValPlWtAddEqZero
import Theorems.Thm_PI_HtPlacesSumWork_valPl_log_le
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
theorem _root_.solution (x : L) : 0 ≤ addv L v x ↔ v.valuation L x ≤ 1 := by
  by_cases hx : x = 0
  · subst hx
    simp
  rw [addv_apply v hx, WithTop.coe_nonneg, neg_nonneg,
    valPl_log_le ((Valuation.ne_zero_iff _).2 hx)]
end PI.HtPlacesSumWork
