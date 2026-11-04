-- Prove2me | solution 1 for ThreeSum.LightSourceResidues.key_cast
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:34:01.294401+00:00
-- url     : https://prove2.me/submissions/73956c30-34ec-4065-aef8-1fd6c6b6b2a1

import Definitions.Def_Submission_ThreeSum_LightResidues
import Definitions.Def_Submission_ThreeSum_LightSourceResidues

set_option autoImplicit false
open ThreeSum ThreeSum.LightSourceResidues
open Light
set_option maxHeartbeats 1200000
set_option maxRecDepth 10000
namespace ThreeSum.LightSourceResidues
theorem _root_.solution {p m : ℕ} (hm : 0 < m) (shift x : ℤ) :
    (key p m shift x : ℤ) = (x % (p : ℤ) + shift) % (m : ℤ) := by
  exact Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast hm.ne'))
end ThreeSum.LightSourceResidues
