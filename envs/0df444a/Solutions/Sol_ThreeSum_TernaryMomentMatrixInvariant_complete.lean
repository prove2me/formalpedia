-- Prove2me | solution 1 for ThreeSum.TernaryMomentMatrixInvariant.complete
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:52:51.831595+00:00
-- url     : https://prove2.me/submissions/7f9497b1-c05b-419c-9386-f7c416d1be9a

import Definitions.Def_Submission_ThreeSum_TernaryMomentSchedule
import Definitions.Def_Submission_ThreeSum_LightTernaryMomentAccumulate
import Definitions.Def_Submission_ThreeSum_TernaryMomentMatrixInvariant
import Theorems.Thm_ThreeSum_TernaryMomentSchedule_channel_rows


set_option autoImplicit false
open ThreeSum ThreeSum.TernaryMomentMatrixInvariant
open Light TernaryMomentSchedule
namespace ThreeSum.TernaryMomentMatrixInvariant
theorem _root_.solution {reference μ : ℕ→ℤ} {matrix count terms boundary : ℕ}
    (score : ℕ→ℕ→ℕ→ℤ)
    (hI : Holds reference matrix count terms boundary (channels terms) score μ) :
    ∀ k<terms, ∀ i<count,
      μ (matrix+k*count+i)=∑ j∈Finset.range (k+1), score k j i := by
  intro k hk i hi
  rw [hI.1 k hk i hi,channel_rows,if_pos hk]
end ThreeSum.TernaryMomentMatrixInvariant
