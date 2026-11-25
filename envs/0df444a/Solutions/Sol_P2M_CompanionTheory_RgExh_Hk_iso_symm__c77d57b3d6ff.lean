-- Prove2me | solution 1 for P2M_CompanionTheory_RgExh_Hk_iso_symm__c77d57b3d6ff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:49:18.199536+00:00
-- url     : https://prove2.me/submissions/65a39806-3f3e-4295-abf0-afe89834deed

import Definitions.Def_CompanionTheory_RealGroups_DiscreteSeries_DiscreteSeriesClassification_DiscreteSeriesExhaustion_HeckeAlgebraActions_BackStable
import Definitions.Def_CompanionTheory_RealGroups_DiscreteSeries_DiscreteSeriesClassification_DiscreteSeriesExhaustion_HeckeAlgebraActions_TensorReflections_PiIsoTensVd

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
theorem _root_.solution {X X' : GMod n} (h : Iso X X') : Iso X' X := by
  obtain ⟨e, he⟩ := h
  refine ⟨e.symm, fun a b x => ?_⟩
  apply e.injective
  rw [he, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
end CompanionTheory.RgExh.Hk
