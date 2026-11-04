-- Prove2me | solution 1 for ThreeSum.WeightedGlobalArenaReporterBounds.arena_geometry
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T16:14:32.842337+00:00
-- url     : https://prove2.me/submissions/9cc986f5-6c44-44f4-ad83-06073d66bc4c

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryPostSelection
import Definitions.Def_Submission_Weighted_Global_TernaryMomentChannelResources
import Definitions.Def_Submission_Weighted_Global_TernaryArenaLayout
import Definitions.Def_Submission_Weighted_Global_TernaryArenaReporterBounds
import Theorems.Thm_ThreeSum_TernarySourceExecutionFactory_Seed_finish
import Theorems.Thm_ThreeSum_WeightedGlobalArenaLayout_before
import Theorems.Thm_ThreeSum_WeightedGlobalArenaLayout_region_space
import Theorems.Thm_ThreeSum_WeightedSourceCountExecutionFactory_Seed_finish


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaReporterBounds
open Light WeightedGlobalArenaLayout LightOriginalSurvivors
open WeightedGlobalNativeMomentBounds WeightedGlobalMomentWeightBounds
namespace ThreeSum.WeightedGlobalArenaReporterBounds
theorem _root_.solution {free C H count nl nr space : ℕ}
    (hcount : (2*H+1)*count≤C) (hterms : 2*H+1≤C)
    (hl : nl≤C) (hr : nr≤C) (hend : finish free C≤space) :
    addr free C 25+(2*H+1)*count≤addr free C 26 ∧
    addr free C 26+(2*H+1)≤space ∧
    addr free C 25+(2*H+1)*count≤addr free C 28 ∧
    addr free C 28+nl≤addr free C 29 ∧ addr free C 29+nr≤space ∧
    addr free C 28≤addr free C 53 ∧ addr free C 53+count≤space ∧
    addr free C 28≤space := by
  have hc : count≤C := by nlinarith only [hcount]
  refine ⟨before (by decide) hcount,region_space (by decide) hterms hend,
    before (by decide) hcount,before (by decide) hl,region_space (by decide) hr hend,
    ?_,region_space (by decide) hc hend,?_⟩
  · exact before (len := 0) (by decide) (by omega)
  · exact region_space (len := 0) (by decide) (by omega) hend
end ThreeSum.WeightedGlobalArenaReporterBounds
