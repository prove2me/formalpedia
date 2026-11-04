-- Prove2me | solution 1 for ThreeSum.LightLeafSum.partialSum_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:56:14.807694+00:00
-- url     : https://prove2.me/submissions/df77ad7b-368f-444e-ad30-3c4ceb8a550a

import Definitions.Def_Submission_ThreeSum_LightSignedLeaf
import Definitions.Def_Submission_ThreeSum_LightLeafSum

set_option autoImplicit false
open ThreeSum ThreeSum.LightLeafSum
open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightLeafSum
theorem _root_.solution {W : ℕ} (Q preL preR : Finset (Fin W))
    (f g : Finset (Fin W) → ℤ) (stage : ℕ) (missing : List (Finset (Fin W))) :
    partialSum Q preL preR f g stage missing missing.length =
      (missing.map (term Q preL preR f g stage)).sum := by
  unfold partialSum
  have he : missing.length = (missing.map (term Q preL preR f g stage)).length :=
    (List.length_map _).symm
  rw [he,List.take_length]
end ThreeSum.LightLeafSum
