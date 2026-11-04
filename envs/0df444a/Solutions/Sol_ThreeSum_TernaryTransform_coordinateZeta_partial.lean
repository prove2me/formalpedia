-- Prove2me | solution 1 for ThreeSum.TernaryTransform.coordinateZeta_partial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:23:37.757415+00:00
-- url     : https://prove2.me/submissions/f25863dd-0bf2-4f54-bac3-69103e8a159d

import Definitions.Def_Submission_ThreeSum_TernaryEuler
import Definitions.Def_Submission_ThreeSum_TernaryTransform
import Theorems.Thm_ThreeSum_TernaryTransform_coordinateZeta_sum
import Theorems.Thm_ThreeSum_TernaryTransform_coordinateZeta_kernel

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryTransform
open Finset
open ThreeSum.TernaryJointType ThreeSum.TernaryQuery ThreeSum.TernaryEuler
namespace ThreeSum.TernaryTransform
theorem _root_.solution {N : ℕ} (s : Finset (Fin N)) (i : Fin N)
    (hi : i ∉ s) (f : TritWord N → ℤ) :
    coordinateZeta i (stageSum s f) = stageSum (insert i s) f := by
  funext R
  unfold stageSum
  rw [coordinateZeta_sum]
  apply Finset.sum_congr rfl
  intro A hA
  exact coordinateZeta_kernel s i hi A R (f A)
end ThreeSum.TernaryTransform
