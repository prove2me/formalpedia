-- Prove2me | solution 1 for ThreeSum.TernaryTransform.runZeta_eq_binomialZeta
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:36:25.318206+00:00
-- url     : https://prove2.me/submissions/842db83e-3ffb-47d4-b277-21db7c22ff63

import Definitions.Def_Submission_ThreeSum_TernaryEuler
import Definitions.Def_Submission_ThreeSum_TernaryTransform
import Theorems.Thm_ThreeSum_TernaryTransform_partial_univ
import Theorems.Thm_ThreeSum_TernaryTransform_runZeta_eq_partial

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryTransform
open Finset
open ThreeSum.TernaryJointType ThreeSum.TernaryQuery ThreeSum.TernaryEuler
namespace ThreeSum.TernaryTransform
theorem _root_.solution {N : ℕ} (coords : List (Fin N))
    (h : coords.Nodup) (hall : coords.toFinset = univ) (f : TritWord N → ℤ) :
    runZeta coords f = binomialZeta f := by
  rw [runZeta_eq_partial coords h, hall, partial_univ]
end ThreeSum.TernaryTransform
