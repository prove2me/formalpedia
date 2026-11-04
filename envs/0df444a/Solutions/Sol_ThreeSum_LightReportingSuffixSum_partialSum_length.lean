-- Prove2me | solution 1 for ThreeSum.LightReportingSuffixSum.partialSum_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:29:04.616804+00:00
-- url     : https://prove2.me/submissions/060943e7-b6e6-4cd8-b3d9-a107b5b8d662

import Definitions.Def_Submission_ThreeSum_LightReportingSuffixCell
import Definitions.Def_Submission_ThreeSum_LightLeafSum
import Definitions.Def_Submission_ThreeSum_LightReportingSuffixSum

set_option autoImplicit false
open ThreeSum ThreeSum.LightReportingSuffixSum
open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress
open ReportingHostSuffix
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightReportingSuffixSum
theorem _root_.solution {W V offset : ℕ} (hfit : offset+V ≤ W) (Q : Finset (Fin V))
    (preL preR : Finset (Fin W)) (f g : Finset (Fin W) → ℤ)
    (stage : ℕ) (missing : List (Finset (Fin V))) :
    partialSum hfit Q preL preR f g stage missing missing.length =
      (missing.map (term hfit Q preL preR f g stage)).sum := by
  unfold partialSum
  have he : missing.length = (missing.map (term hfit Q preL preR f g stage)).length :=
    (List.length_map _).symm
  rw [he,List.take_length]
end ThreeSum.LightReportingSuffixSum
