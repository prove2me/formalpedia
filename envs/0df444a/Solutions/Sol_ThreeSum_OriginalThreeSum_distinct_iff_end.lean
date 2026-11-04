-- Prove2me | solution 1 for ThreeSum.OriginalThreeSum.distinct_iff_end
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:07:17.710769+00:00
-- url     : https://prove2.me/submissions/70fe9b13-04ed-4585-b61d-1bbd85dcabf7

import Definitions.Def_Submission_ThreeSum_Coloring
import Definitions.Def_Submission_ThreeSumApsp_Programs_Tasks
import Definitions.Def_Submission_ThreeSum_OriginalThreeSum

set_option autoImplicit false
open ThreeSum ThreeSum.OriginalThreeSum
open Light ThreeSumApsp.Spec
namespace ThreeSum.OriginalThreeSum
theorem _root_.solution {n : ℕ} (x : Fin n → ℤ) :
    Coloring.DistinctZeroSum x ↔ EndStatement.ThreeSum.yes x := by
  constructor
  · rintro ⟨i,j,k,hij,hik,hjk,hzero⟩
    exact ⟨i,j,k,hij,hjk,hik,hzero⟩
  · rintro ⟨i,j,k,hij,hjk,hik,hzero⟩
    exact ⟨i,j,k,hij,hik,hjk,hzero⟩
end ThreeSum.OriginalThreeSum
