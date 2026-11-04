-- Prove2me | solution 1 for ThreeSum.TernaryTypeLowerBound.partition_cap_le_prime
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:04:00.39697+00:00
-- url     : https://prove2.me/submissions/a680969b-7364-4b6b-b40a-5aff0a050c99

import Definitions.Def_Submission_ThreeSum_TernaryCoverOutputCap
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_TernaryTypeLowerBound
import Theorems.Thm_ThreeSum_TernaryTypeLowerBound_vertices_lower_bound

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryTypeLowerBound
open Finset TernaryJointType TernaryCoverLocal
namespace ThreeSum.TernaryTypeLowerBound
theorem _root_.solution {L : ℕ} (π : DigitType)
    (htotal : π 0+π 1+π 2 = L) (hspace : 2*(π 1)+3*(π 2) ≤ L)
    (P : ℕ) (hP : (vertices L π).card*(2^(π 1)*3^(π 2)) ≤ P^2) :
    2^(π 1)*3^(π 2) ≤ P := by
  have h := vertices_lower_bound π htotal hspace
  nlinarith
end ThreeSum.TernaryTypeLowerBound
