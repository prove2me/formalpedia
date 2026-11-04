-- Prove2me | solution 1 for ThreeSum.TernaryActualSeedEnumeration.index_mod
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:17:49.189929+00:00
-- url     : https://prove2.me/submissions/0b24c9ad-c477-40f5-9445-1c6245607418

import Definitions.Def_Submission_ThreeSum_TernaryOriginalKeyCodes
import Definitions.Def_Submission_ThreeSum_LightExtensionSeedMatrix
import Definitions.Def_Submission_ThreeSum_TernaryActualSeedEnumeration
import Theorems.Thm_ThreeSum_TernaryActualSeedEnumeration_index_value

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryActualSeedEnumeration
open TernaryExtensionEncoding Polynomial
open scoped BigOperators
variable {p : ℕ} [Fact p.Prime] {f : (ZMod p)[X]}
variable [Fact (Irreducible f)] [Fintype (AdjoinRoot f)]
set_option maxHeartbeats 2000000
namespace ThreeSum.TernaryActualSeedEnumeration
theorem _root_.solution (hf : f.Monic) (x y : AdjoinRoot f) :
    (equiv hf (x,y)).val%(p^f.natDegree)=encode hf y := by
  rw [index_value,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt (encode_lt hf y)]
end ThreeSum.TernaryActualSeedEnumeration
