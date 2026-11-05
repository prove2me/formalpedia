-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedSchedule.query_outside
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T10:18:08.183904+00:00
-- url     : https://prove2.me/submissions/c05e7279-a297-48c6-88ba-797960481202

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_BankEnumeration
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_NearBankEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryEuler
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Schedule
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedSchedule_output_cost

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedSchedule
open TernaryJointType WeightedBankEnumeration
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedSchedule
theorem _root_.solution {m : ℕ} {Q : TritWord (fixedLength m)}
    (hm : 0<m) (hQ : HasType Q (fixedPi m)) : bankCut m<cacheCost Q := by
  rw [output_cost hQ]; unfold dropBudget; omega
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedSchedule
