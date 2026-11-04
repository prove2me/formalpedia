-- Prove2me | solution 1 for ThreeSum.BlockForced.residual_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:56:49.10868+00:00
-- url     : https://prove2.me/submissions/87392cc1-2f40-4e9f-b8fe-de82397ad543

import Definitions.Def_Submission_ThreeSum_BlockEncoding
import Definitions.Def_Submission_ThreeSum_BlockForced
import Theorems.Thm_ThreeSum_BlockForced_residual_subset
import Theorems.Thm_ThreeSum_BlockForced_forced_left_completion
import Theorems.Thm_ThreeSum_BlockForced_forced_right_completion
import Theorems.Thm_ThreeSum_BlockEncoding_leftAllowed_choice
import Theorems.Thm_ThreeSum_BlockEncoding_rightAllowed_choice


set_option autoImplicit false
open ThreeSum ThreeSum.BlockForced
set_option maxRecDepth 8000
open Finset
open scoped BigOperators
open GlobalEncoding LocalGraph LocalCoverBounds RawIncidences RawReporting RawPrefixCounts
open BlockRows BlockEncoding
namespace ThreeSum.BlockForced
theorem _root_.solution {h J : ℕ} (q : GlobalOutput h J) (I : Finset (Fin J))
    (u : Fin J → Finset (Fin (512 * h)))
    (hu : ∀ i ∈ I, u i ⊆ outputRows q i) (t : ChoiceTuple h J)
    (ht : t ∈ completedTuples q I u) : residual I t ∈ admissibleResiduals q I u := by
  have hq := (Finset.mem_filter.mp ht).2.1
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_powerset.mpr (residual_subset q I t hq), ?_⟩
  rw [forced_left_completion q I u t ht, forced_right_completion q I u hu t ht]
  exact ⟨leftAllowed_choice t q hq, rightAllowed_choice t q hq⟩
end ThreeSum.BlockForced
