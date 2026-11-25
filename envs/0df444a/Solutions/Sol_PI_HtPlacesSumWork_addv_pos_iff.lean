-- Prove2me | solution 1 for PI.HtPlacesSumWork.addv_pos_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:49:46.031038+00:00
-- url     : https://prove2.me/submissions/40195d57-c815-4bed-aa0d-a02044e7b6ed

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_TheoremA
import Definitions.Def_ReciprocityTheory_SemistableReduction_AlgAll
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GaussHeights_PlaceSumHeights_PlaceSumStatements_PlaceSumLemmas_GaussValuationSums_ValPlWtAddEqZero
import Theorems.Thm_PI_HtPlacesSumWork_valPl_log_lt
import Theorems.Thm_PI_HtPlacesSumWork_addv_alg

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
theorem _root_.solution (s : S) : 0 < addv L v (algebraMap S L s) ↔ s ∈ v.asIdeal := by
  by_cases hs : s = 0
  · subst hs
    simp
  rw [addv_alg v hs, WithTop.coe_pos, neg_pos, ← valPl_log_lt (v.intValuation_ne_zero s hs),
    HeightOneSpectrum.intValuation_lt_one_iff_mem]
end PI.HtPlacesSumWork
