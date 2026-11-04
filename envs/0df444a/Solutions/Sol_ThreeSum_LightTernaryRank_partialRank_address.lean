-- Prove2me | solution 1 for ThreeSum.LightTernaryRank.partialRank_address
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:38:30.210236+00:00
-- url     : https://prove2.me/submissions/c1cf4d0c-0661-42fe-be5f-4234ac029cbd

import Definitions.Def_Submission_ThreeSum_TernaryCodeSemantics
import Definitions.Def_Submission_ThreeSum_LightTernaryRank
import Theorems.Thm_ThreeSum_TernaryCodeSemantics_digit_eq


set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryRank
open Light Finset ThreeSum.TernaryJointType ThreeSum.TernaryBank
open ThreeSum.TernaryCodeSemantics ThreeSum.LightSubsetAddress
namespace ThreeSum.LightTernaryRank
theorem _root_.solution {N : ℕ} (w : TritWord N) : partialRank N (address w) N=rank w := by
  unfold partialRank rank
  rw [← Fin.sum_univ_eq_sum_range]
  apply sum_congr rfl
  intro i hi
  exact digit_eq w i
end ThreeSum.LightTernaryRank
