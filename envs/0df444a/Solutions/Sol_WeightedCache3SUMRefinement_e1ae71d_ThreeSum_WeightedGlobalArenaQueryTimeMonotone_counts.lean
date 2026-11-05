-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaQueryTimeMonotone.counts
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:51:27.11207+00:00
-- url     : https://prove2.me/submissions/de5c3fc6-14ef-4458-b9cb-be16d5639543

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaQueryTime
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaPostSelection
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaQueryTimeMonotone
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaQueryTimeMonotone_query
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaQueryTimeMonotone_value

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaQueryTimeMonotone
open WeightedGlobalArenaSourceSetup WeightedGlobalCoverGoodMaps WeightedGlobalLocalParameters TernaryJointType
variable {p m F r : ℕ} [Fact p.Prime]
set_option maxHeartbeats 6000000
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaQueryTimeMonotone
theorem _root_.solution (maps : Fin F→Weight m p) (cap : ℕ) (I I' : Input)
    (hB : I.nB≤I'.nB) (hC : I.nC≤I'.nC) (hw : I.weightCap≤I'.weightCap) :
    WeightedGlobalArenaCountReady.queryTime (m:=m) (r:=r) I (valueCap (r:=r) maps cap I)≤
      WeightedGlobalArenaCountReady.queryTime (m:=m) (r:=r) I' (valueCap (r:=r) maps cap I') :=
  query I I' (value maps cap I I' hB hC hw)
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaQueryTimeMonotone
