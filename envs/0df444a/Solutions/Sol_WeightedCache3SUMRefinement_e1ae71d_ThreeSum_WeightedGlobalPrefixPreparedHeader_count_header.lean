-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalPrefixPreparedHeader.count_header
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T14:46:29.507359+00:00
-- url     : https://prove2.me/submissions/6afc1998-0f07-4181-af2f-5349e6451c84

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaHeaderAgreement
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryPrefixPrepare
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryPrefixPreparedHeader
import Theorems.Thm_Light_LocalsBut_update
import Theorems.Thm_ThreeSum_LightTernarySourceCountHost_Reads_update
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedGlobalPrefixHeader_store_seg
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedSourceCountHost_Reads_update
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaHeaderAgreement_argv_agreement


set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalPrefixPreparedHeader
open Light WeightedGlobalArenaLayout WeightedGlobalArenaSourceSetup WeightedGlobalArenaHeaderAgreement
set_option maxHeartbeats 6000000
set_option maxRecDepth 24000
variable {p m F : ℕ} [Fact p.Prime]
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalPrefixPreparedHeader
theorem _root_.solution {ν : ℕ→ℤ} (I : Input) (j : ℕ)
    (maps : Fin F→WeightedGlobalCoverGoodMaps.Weight m p) (τ cap : ℕ)
    (Q : WeightedGlobalGoodOutputCatalog.Output m) (ret : ℤ)
    (hs : Seg ν (addr I.free I.capacity 1) (emittedHeader I p m F j Q ret)) :
    Seg (Function.update ν (addr I.free I.capacity 1+104)
      ((entries (r:=j+1) maps τ I).length:ℤ)) (addr I.free I.capacity 1)
      (setup (r:=j+1) maps τ cap Q I).argv :=by
  rw [← argv_agreement maps τ cap j Q I ret]
  exact LightWeightedGlobalPrefixHeader.store_seg hs 104 _
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalPrefixPreparedHeader
