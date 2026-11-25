-- Prove2me | solution 1 for P2M_CompanionTheory_RgExh_Hk_reflect_of__e60226858e99
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:26:02.71319+00:00
-- url     : https://prove2.me/submissions/6be6291a-3c63-4447-bd67-1b02bb984894

import Definitions.Def_CompanionTheory_RealGroups_DiscreteSeries_DiscreteSeriesClassification_DiscreteSeriesExhaustion_HeckeAlgebraActions_BackStable
import Definitions.Def_CompanionTheory_RealGroups_DiscreteSeries_DiscreteSeriesClassification_DiscreteSeriesExhaustion_HeckeAlgebraActions_TensorReflections_PiIsoTensVd
import Theorems.Thm_P2M_CompanionTheory_RgExh_Hk_iso_symm__c77d57b3d6ff
import Theorems.Thm_P2M_CompanionTheory_RgExh_Hk_iso_trans__11fe56a408d0
import Theorems.Thm_P2M_CompanionTheory_RgExh_Hk_iso_back__c404c772443b

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CompanionTheory CompanionTheory.RgExh CompanionTheory.RgExh.Hk
open ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
variable {n : ℕ}
namespace CompanionTheory.RgExh.Hk
theorem _root_.solution : QdetTens → OmScal → BackStable → DualFacts → Hk.Unit → Reflect := by
  intro _ hOm hB _ hU n X X' χ s hX hX' hfree hsimp hiso
  have h1 := hU n X χ s hB hX hfree hsimp (hOm n X χ s hX hsimp)
  have h2 := hU n X' χ s hB hX' hfree hsimp (hOm n X' χ s hX' hsimp)
  exact iso_trans' (iso_symm' h1) (iso_trans' (iso_back' hiso _ _ _) h2)
end CompanionTheory.RgExh.Hk
