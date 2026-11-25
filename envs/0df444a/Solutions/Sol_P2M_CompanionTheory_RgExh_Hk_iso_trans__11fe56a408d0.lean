-- Prove2me | solution 1 for P2M_CompanionTheory_RgExh_Hk_iso_trans__11fe56a408d0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:55:16.095136+00:00
-- url     : https://prove2.me/submissions/00c07618-926f-4a7f-8b53-8ca6fc7cd8a5

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
theorem _root_.solution {X X' X'' : GMod n} (h : Iso X X') (h' : Iso X' X'') : Iso X X'' := by
  obtain ⟨e, he⟩ := h
  obtain ⟨e', he'⟩ := h'
  exact ⟨e.trans e', fun a b x => by simp [he, he']⟩
end CompanionTheory.RgExh.Hk
