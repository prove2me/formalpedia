-- Prove2me | solution 1 for ThreeSum.TernaryActualSeedEnumeration.matrix_row
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:22:07.490189+00:00
-- url     : https://prove2.me/submissions/82540951-413e-450e-947b-19cb1b7e958d

import Definitions.Def_Submission_ThreeSum_TernaryOriginalKeyCodes
import Definitions.Def_Submission_ThreeSum_LightExtensionSeedMatrix
import Definitions.Def_Submission_ThreeSum_TernaryActualSeedEnumeration
import Theorems.Thm_ThreeSum_TernaryActualSeedEnumeration_index_div
import Theorems.Thm_ThreeSum_TernaryActualSeedEnumeration_index_mod
import Theorems.Thm_ThreeSum_TernaryExtensionEncoding_trajectory_rowMenu


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryActualSeedEnumeration
open TernaryExtensionEncoding Polynomial
open scoped BigOperators
variable {p : ℕ} [Fact p.Prime] {f : (ZMod p)[X]}
variable [Fact (Irreducible f)] [Fintype (AdjoinRoot f)]
set_option maxHeartbeats 2000000
namespace ThreeSum.TernaryActualSeedEnumeration
theorem _root_.solution (hf : f.Monic) (hd : 0<f.natDegree) (J : ℕ)
    (x y : AdjoinRoot f) (i : Fin (J+2)) :
    LightExtensionSeedMatrix.value (encodedMul hf) (p^f.natDegree) p
      (equiv hf (x,y)).val (TernarySignedLayout.offset J i.val)=
      (TernaryOriginalRowMenu.seedRow (J+2) (constantCoefficient hf hd) (x,y)
        (digitOrder J i)).val := by
  unfold LightExtensionSeedMatrix.value
  rw [index_div,index_mod]
  exact trajectory_rowMenu hf hd (J+2) x y (digitOrder J i)
end ThreeSum.TernaryActualSeedEnumeration
