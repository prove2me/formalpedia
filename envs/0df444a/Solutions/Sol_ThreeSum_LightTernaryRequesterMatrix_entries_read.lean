-- Prove2me | solution 1 for ThreeSum.LightTernaryRequesterMatrix.entries_read
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:47:06.246736+00:00
-- url     : https://prove2.me/submissions/8ab4fe87-d9ad-4066-9078-f85efbd125f7

import Definitions.Def_Submission_ThreeSum_LightTernaryOriginalRequester
import Definitions.Def_Submission_ThreeSum_LightTernaryCarryCodes
import Definitions.Def_Submission_ThreeSum_LightTernarySignedMatrix
import Definitions.Def_Submission_ThreeSum_TernarySignedLayout
import Definitions.Def_Submission_ThreeSum_LightTernaryRequesterMatrix
import Theorems.Thm_ThreeSum_TernarySignedLayout_row_physical_read


set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryRequesterMatrix
open Light TernarySignedDigits TernarySignedReduction
set_option maxHeartbeats 6000000
set_option maxRecDepth 10000
variable {lim : Limits} {P : Program} {depth : ℕ}
namespace ThreeSum.LightTernaryRequesterMatrix
theorem _root_.solution {μ : ℕ → ℤ} {positions matrix J Q len U radix : ℕ} {f : ℕ → ℤ}
    (H : Entries μ positions matrix J Q len U radix f) :
    (∀row<len, ∀coordinate<J+2,
      μ (matrix+row*(J+2)+coordinate)=value U radix J Q f row coordinate) ∧
      (∀row<len, μ (positions+row)=(row/Q : ℕ)) := by
  refine ⟨?_,fun row hr => (H row hr).2⟩
  intro row hr coordinate hc
  exact TernarySignedLayout.row_physical_read (H row hr).1 hc
end ThreeSum.LightTernaryRequesterMatrix
