-- Prove2me | solution 1 for ThreeSum.LightSourceRetainedStages.source_abs_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:55:35.754101+00:00
-- url     : https://prove2.me/submissions/79538efb-1607-4641-bc7c-670bd4fedba3

import Definitions.Def_Submission_ThreeSum_LightSourceStages
import Definitions.Def_Submission_ThreeSum_LightSourceRetainedStages
import Theorems.Thm_ThreeSum_LightResidues_residue_lt


set_option autoImplicit false
open ThreeSum ThreeSum.LightSourceRetainedStages
open Light SubsetAddress LightSubsetAddress LightPascal LightZetaCell
set_option maxHeartbeats 1800000
set_option maxRecDepth 12000
namespace ThreeSum.LightSourceRetainedStages
theorem _root_.solution {L m B : ℕ} (hm : 0 < m)
    (endpoint : Finset (Fin L) → ℤ) (flag : Finset (Fin L) → ℕ) (hist : ℕ → ℕ)
    (hhist : ∀ r < m, hist r ≤ B) (S : Finset (Fin L)) :
    |source m endpoint flag hist S| ≤ (B : ℤ) := by
  unfold source
  rw [Int.abs_natCast]
  apply Int.ofNat_le.mpr
  split
  · exact hhist _ (LightResidues.residue_lt hm 1 _)
  · omega
end ThreeSum.LightSourceRetainedStages
