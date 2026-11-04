-- Prove2me | solution 1 for ThreeSum.LightSourceStages.source_abs_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:56:11.308033+00:00
-- url     : https://prove2.me/submissions/b7e46577-076d-4832-9d52-5889a12bc24e

import Definitions.Def_Submission_ThreeSum_LightSourceBuild
import Definitions.Def_Submission_ThreeSum_SourceTableLayout
import Definitions.Def_Submission_ThreeSum_LightZetaStages
import Definitions.Def_Submission_ThreeSum_LightSourceStages
import Theorems.Thm_ThreeSum_LightHistogram_count_le


set_option autoImplicit false
open ThreeSum ThreeSum.LightSourceStages
open Light SubsetAddress LightSubsetAddress LightPascal LightZetaCell
set_option maxHeartbeats 2200000
set_option maxRecDepth 12000
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightSourceStages
theorem _root_.solution {L : ℕ} (μ : ℕ → ℤ) (src N p m : ℕ) (shift : ℤ)
    (endpoint : Finset (Fin L) → ℤ) (flag : Finset (Fin L) → ℕ)
    (S : Finset (Fin L)) : |source μ src N p m shift endpoint flag S| ≤ (N : ℤ) := by
  unfold source
  rw [Int.abs_natCast]
  apply Int.ofNat_le.mpr
  split
  · exact LightHistogram.count_le ..
  · omega
end ThreeSum.LightSourceStages
