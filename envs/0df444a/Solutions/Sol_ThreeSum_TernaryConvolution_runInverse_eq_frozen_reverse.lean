-- Prove2me | solution 1 for ThreeSum.TernaryConvolution.runInverse_eq_frozen_reverse
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:36:38.031728+00:00
-- url     : https://prove2.me/submissions/20afec8b-50af-4a3f-a398-542f37a7ba54

import Definitions.Def_Submission_ThreeSum_TernaryReconstruction
import Definitions.Def_Submission_ThreeSum_TernaryTransform
import Mathlib.Algebra.BigOperators.Finprod
import Definitions.Def_Submission_ThreeSum_TernaryConvolution
import Theorems.Thm_ThreeSum_TernaryConvolution_frozenInverse_append

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryConvolution
open Finset ThreeSum.TernaryJointType ThreeSum.TernaryBank
open ThreeSum.TernaryEuler ThreeSum.TernaryQuery ThreeSum.TernaryReconstruction
set_option maxHeartbeats 2000000
namespace ThreeSum.TernaryConvolution
theorem _root_.solution {N : ℕ} (coords : List (Fin N))
    (H : TritWord N → ℤ) : runInverse coords H=frozenInverse coords.reverse H := by
  induction coords generalizing H with
  | nil => rfl
  | cons i rest ih =>
    rw [runInverse,ih,List.reverse_cons,frozenInverse_append]
    rfl
end ThreeSum.TernaryConvolution
