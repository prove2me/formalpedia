-- Prove2me | solution 1 for ThreeSum.LocalParameterBounds.cap_word_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:05:15.108212+00:00
-- url     : https://prove2.me/submissions/038fb722-6720-432d-9a71-9e958fdcd650

import Definitions.Def_Submission_ThreeSum_LightLocalParameters
import Definitions.Def_Submission_ThreeSum_Scales
import Definitions.Def_Submission_ThreeSum_LocalParameterBounds
import Theorems.Thm_ThreeSum_LocalParameterBounds_pow_pos
import Theorems.Thm_ThreeSum_LocalParameterBounds_vertex_bound
import Theorems.Thm_ThreeSum_LocalParameterBounds_prime_bound

set_option autoImplicit false
open ThreeSum ThreeSum.LocalParameterBounds
open LocalCoverBounds
set_option maxHeartbeats 1000000
namespace ThreeSum.LocalParameterBounds
theorem _root_.solution (h : ℕ) :
    20*(localPrime h+vertexCount (512*h) h+1) ≤ 2^(514*h+7) := by
  have hp := prime_bound h
  have hv := vertex_bound h
  have hx := pow_pos (514*h)
  rw [pow_add] at hp
  norm_num at hp
  rw [pow_add]
  norm_num
  omega
end ThreeSum.LocalParameterBounds
