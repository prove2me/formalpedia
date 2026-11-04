-- Prove2me | solution 1 for ThreeSum.SourceBandPartition.source_unique
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:54:12.464654+00:00
-- url     : https://prove2.me/submissions/63376be9-cadb-4455-ad02-ceb90d894ce2

import Definitions.Def_Submission_ThreeSum_SourceBandLayout
import Definitions.Def_Submission_ThreeSum_SourceBandPartition

set_option autoImplicit false
open ThreeSum ThreeSum.SourceBandPartition
open BandPartition SourceBandLayout
namespace ThreeSum.SourceBandPartition
theorem _root_.solution {n g i j : ℕ} {t : Fin n}
    (hi : t ∈ source n g i) (hj : t ∈ source n g j) : i=j := by
  obtain ⟨hil,hih⟩ := mem_source.mp hi
  obtain ⟨hjl,hjh⟩ := mem_source.mp hj
  have his : stop n g i ≤ (i+1)*g := min_le_right _ _
  have hjs : stop n g j ≤ (j+1)*g := min_le_right _ _
  rcases lt_trichotomy i j with h | h | h
  · have hp := Nat.mul_le_mul_right g (show i+1 ≤ j by omega)
    unfold start at *
    omega
  · exact h
  · have hp := Nat.mul_le_mul_right g (show j+1 ≤ i by omega)
    unfold start at *
    omega
end ThreeSum.SourceBandPartition
