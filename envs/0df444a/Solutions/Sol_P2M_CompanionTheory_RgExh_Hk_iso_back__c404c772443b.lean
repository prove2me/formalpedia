-- Prove2me | solution 1 for P2M_CompanionTheory_RgExh_Hk_iso_back__c404c772443b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:06:43.324661+00:00
-- url     : https://prove2.me/submissions/7ba4eacf-8c19-4836-8fba-4bdb7ce51f42

import Definitions.Def_CompanionTheory_RealGroups_DiscreteSeries_DiscreteSeriesClassification_DiscreteSeriesExhaustion_HeckeAlgebraActions_BackStable
import Definitions.Def_CompanionTheory_RealGroups_DiscreteSeries_DiscreteSeriesClassification_DiscreteSeriesExhaustion_HeckeAlgebraActions_TensorReflections_PiIsoTensVd
import Theorems.Thm_CompanionTheory_RgExh_Hk_map_maxGen
import Theorems.Thm_P2M_CompanionTheory_RgExh_Hk_iso_sub__48260da7f134
import Theorems.Thm_CompanionTheory_RgExh_Hk_piIso_tensVd
import Theorems.Thm_CompanionTheory_RgExh_Hk_piIso_eeVd

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
theorem _root_.solution {Y Y' : GMod n} (hY : Iso Y Y') (z : ℂ)
    (h : ∀ a b, ∀ x ∈ backSub Y z, (tensD Y).E a b x ∈ backSub Y z)
    (h' : ∀ a b, ∀ x ∈ backSub Y' z, (tensD Y').E a b x ∈ backSub Y' z) :
    Iso (back Y z h) (back Y' z h') := by
  obtain ⟨e, he⟩ := hY
  exact iso_sub' (X := tensD Y) (X' := tensD Y') (piIso e) (fun a b f => piIso_tensVd e he a b f) _ _
    (map_maxGen (piIso e) (omD Y) (omD Y') (fun f => piIso_eeVd e he f) _) h h'
end CompanionTheory.RgExh.Hk
