-- Prove2me | solution 1 for ThreeSum.TernaryExtensionEncoding.trajectory_constantCoefficient
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:29:55.707481+00:00
-- url     : https://prove2.me/submissions/35a307a9-bd8b-4fe1-911d-4279c28cf0ad

import Definitions.Def_Submission_ThreeSum_TernaryExtensionSearchCorrect
import Definitions.Def_Submission_ThreeSum_TernaryOriginalRowMenu
import Definitions.Def_Submission_ThreeSum_LightExtensionSeedRow
import Definitions.Def_Submission_ThreeSum_LightNaturalDot
import Definitions.Def_Submission_ThreeSum_TernaryExtensionSeedSemantics
import Theorems.Thm_ThreeSum_TernaryExtensionEncoding_trajectory_encode
import Theorems.Thm_ThreeSum_TernaryExtensionEncoding_encode_mod


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryExtensionEncoding
open Polynomial Finset
open scoped BigOperators
variable {p : ℕ} [Fact p.Prime]
set_option maxHeartbeats 3000000
attribute [local instance] ThreeSum.TernaryExtensionEncoding._p2m_local_instance_7138b7e7ca_12
variable {f : (ZMod p)[X]}
namespace ThreeSum.TernaryExtensionEncoding
theorem _root_.solution (hf : f.Monic) (hd : 0<f.natDegree)
    (x y : AdjoinRoot f) (i : ℕ) :
    (LightExtensionSeedRow.trajectory (encodedMul hf) (encode hf x) (encode hf y) i)%p=
      (constantCoefficient hf hd (y*x^i)).val := by
  rw [trajectory_encode,encode_mod]
end ThreeSum.TernaryExtensionEncoding
