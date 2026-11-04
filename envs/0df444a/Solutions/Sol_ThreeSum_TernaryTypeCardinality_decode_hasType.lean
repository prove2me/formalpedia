-- Prove2me | solution 1 for ThreeSum.TernaryTypeCardinality.decode_hasType
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:00:55.636531+00:00
-- url     : https://prove2.me/submissions/24f58c16-7106-4399-a364-5774d220d5a9

import Definitions.Def_Submission_ThreeSum_TernaryCoverLocal
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sigma
import Definitions.Def_Submission_ThreeSum_TernaryTypeCardinality
import Theorems.Thm_ThreeSum_TernaryTypeCardinality_positions_card
import Theorems.Thm_ThreeSum_TernaryTypeCardinality_digitCount_total
import Theorems.Thm_ThreeSum_TernaryTypeCardinality_mem_digitPairs
import Theorems.Thm_ThreeSum_TernaryTypeCardinality_positions_decode_two
import Theorems.Thm_ThreeSum_TernaryTypeCardinality_positions_decode_one

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryTypeCardinality
open Finset ThreeSum.TernaryJointType ThreeSum.TernaryCoverLocal
set_option maxHeartbeats 2000000
namespace ThreeSum.TernaryTypeCardinality
theorem _root_.solution {L : ℕ} (π : DigitType) (htotal : π 0+π 1+π 2=L)
    (p : Pair L) (hp : p∈digitPairs L (π 1) (π 2)) : HasType (decode p) π := by
  obtain ⟨h2,h1,hd⟩ := (mem_digitPairs p).mp hp
  have htwo : digitCount (decode p) 2=π 2 := by
    rw [←positions_card,positions_decode_two,h2]
  have hone : digitCount (decode p) 1=π 1 := by
    rw [←positions_card,positions_decode_one p hd,h1]
  have hz := digitCount_total (decode p)
  have hzero : digitCount (decode p) 0=π 0 := by omega
  intro d
  fin_cases d
  · exact hzero
  · exact hone
  · exact htwo
end ThreeSum.TernaryTypeCardinality
