-- Prove2me | solution 1 for ThreeSum.LightBoxSum.partialSum_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:53:04.96103+00:00
-- url     : https://prove2.me/submissions/d47c6ae4-3edb-4ee8-81b5-8039e2a69f0d

import Definitions.Def_Submission_ThreeSum_LightQueryBox
import Definitions.Def_Submission_ThreeSum_BoxBounds
import Definitions.Def_Submission_ThreeSum_LightBoxSum

set_option autoImplicit false
open ThreeSum ThreeSum.LightBoxSum
open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightBoxSum
theorem _root_.solution {L : ℕ} (Q : Finset (Fin L)) (weight : Finset (Fin L) → ℤ)
    (missing : List (Finset (Fin L))) :
    partialSum Q weight missing missing.length = (missing.map (boxValue Q weight)).sum := by
  unfold partialSum
  have he : missing.length = (missing.map (boxValue Q weight)).length := (List.length_map _).symm
  rw [he,List.take_length]
end ThreeSum.LightBoxSum
