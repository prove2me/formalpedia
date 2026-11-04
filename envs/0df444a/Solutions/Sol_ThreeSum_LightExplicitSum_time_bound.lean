-- Prove2me | solution 1 for ThreeSum.LightExplicitSum.time_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:23:44.576107+00:00
-- url     : https://prove2.me/submissions/a0d9537c-45c2-4637-9cfe-bf292d93a69b

import Definitions.Def_Submission_ThreeSum_ExplicitLayers
import Definitions.Def_Submission_ThreeSum_LightLeafSum
import Definitions.Def_Submission_ThreeSum_LightQueryEnumeration
import Definitions.Def_Submission_ThreeSum_LightExplicitSum

set_option autoImplicit false
open ThreeSum ThreeSum.LightExplicitSum
open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress
open QueryCoordinates
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightExplicitSum
theorem _root_.solution {W c t : ℕ} (ht : t ≤ W+1) :
    time W c t ≤ 8200*(W+1)^3*(layerOffset c t+1) := by
  have hp : 1 ≤ (W+1)^2*(layerOffset c t+1) := Nat.mul_pos (by positivity) (by omega)
  have hm := Nat.mul_le_mul_right (roundTime W c t+30) ht
  unfold time roundTime at *
  nlinarith
end ThreeSum.LightExplicitSum
