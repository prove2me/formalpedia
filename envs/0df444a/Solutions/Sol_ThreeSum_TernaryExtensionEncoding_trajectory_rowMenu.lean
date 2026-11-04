-- Prove2me | solution 1 for ThreeSum.TernaryExtensionEncoding.trajectory_rowMenu
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:34:21.195211+00:00
-- url     : https://prove2.me/submissions/fbdf6bfb-3412-491d-9adf-3d0c60c5dbc9

import Definitions.Def_Submission_ThreeSum_TernaryExtensionSearchCorrect
import Definitions.Def_Submission_ThreeSum_TernaryOriginalRowMenu
import Definitions.Def_Submission_ThreeSum_LightExtensionSeedRow
import Definitions.Def_Submission_ThreeSum_LightNaturalDot
import Definitions.Def_Submission_ThreeSum_TernaryExtensionSeedSemantics
import Theorems.Thm_ThreeSum_TernaryExtensionEncoding_trajectory_constantCoefficient
import Theorems.Thm_ThreeSum_TernaryExtensionEncoding_rowMenu_coefficient

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryExtensionEncoding
open Polynomial Finset
open scoped BigOperators
variable {p : ℕ} [Fact p.Prime]
set_option maxHeartbeats 3000000
attribute [local instance] ThreeSum.TernaryExtensionEncoding._p2m_local_instance_7138b7e7ca_12
variable {f : (ZMod p)[X]}
variable [Fact (Irreducible f)] [Fintype (AdjoinRoot f)]
namespace ThreeSum.TernaryExtensionEncoding
theorem _root_.solution (hf : f.Monic) (hd : 0<f.natDegree) (Λ : ℕ)
    (x y : AdjoinRoot f) (i : Fin Λ) :
    (LightExtensionSeedRow.trajectory (encodedMul hf) (encode hf x) (encode hf y) i.val)%p=
      (TernaryOriginalRowMenu.seedRow Λ (constantCoefficient hf hd) (x,y) i).val := by
  rw [rowMenu_coefficient,trajectory_constantCoefficient]
end ThreeSum.TernaryExtensionEncoding
