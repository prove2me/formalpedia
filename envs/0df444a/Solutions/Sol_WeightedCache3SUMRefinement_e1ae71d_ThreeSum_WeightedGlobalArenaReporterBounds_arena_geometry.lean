-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaReporterBounds.arena_geometry
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T12:51:55.311203+00:00
-- url     : https://prove2.me/submissions/c2055594-782b-4da9-9a1e-1945b3ea0880

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryPostSelection
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryMomentChannelResources
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaLayout
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaReporterBounds
import Theorems.Thm_ThreeSum_TernarySourceExecutionFactory_Seed_finish
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaLayout_before
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaLayout_region_space
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedSourceCountExecutionFactory_Seed_finish


set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaReporterBounds
open Light WeightedGlobalArenaLayout LightOriginalSurvivors
open WeightedGlobalNativeMomentBounds WeightedGlobalMomentWeightBounds
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaReporterBounds
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
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaReporterBounds
