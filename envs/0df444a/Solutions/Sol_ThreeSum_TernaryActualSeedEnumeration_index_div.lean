-- Prove2me | solution 1 for ThreeSum.TernaryActualSeedEnumeration.index_div
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:17:24.026224+00:00
-- url     : https://prove2.me/submissions/a75b4e5b-8a51-415d-9fa1-19a63034ff25

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
    (equiv hf (x,y)).val/(p^f.natDegree)=encode hf x := by
  rw [index_value,Nat.add_mul_div_left _ _ (by have := (Fact.out : p.Prime).pos; positivity),
    Nat.div_eq_of_lt (encode_lt hf y),Nat.zero_add]
end ThreeSum.TernaryActualSeedEnumeration
