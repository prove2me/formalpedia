-- Prove2me | solution 1 for PI.HtPlacesSumWork.addv_isNormDiscrete
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:33:38.144747+00:00
-- url     : https://prove2.me/submissions/e6fddec9-e234-4204-a2a9-51d114b5af6b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_TheoremA
import Definitions.Def_ReciprocityTheory_SemistableReduction_AlgAll
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GaussHeights_PlaceSumHeights_PlaceSumStatements_PlaceSumLemmas_GaussValuationSums_ValPlWtAddEqZero
import Theorems.Thm_PI_HtPlacesSumWork_addv_apply
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
theorem _root_.solution : IsNormDiscrete (addv L v) := by
  refine ⟨fun a ha => by rw [addv_apply v ha]; exact WithTop.coe_ne_top, ?_⟩
  obtain ⟨π, hπ⟩ := v.intValuation_exists_uniformizer
  have hπ0 : π ≠ 0 := by
    rintro rfl
    simp at hπ
    exact WithZero.exp_ne_zero hπ.symm
  exact ⟨algebraMap S L π, by rw [addv_alg v hπ0, hπ, log_exp]; rfl⟩
end PI.HtPlacesSumWork
