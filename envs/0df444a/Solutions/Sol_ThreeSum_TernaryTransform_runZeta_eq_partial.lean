-- Prove2me | solution 1 for ThreeSum.TernaryTransform.runZeta_eq_partial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:35:22.0324+00:00
-- url     : https://prove2.me/submissions/b665c1d1-bcba-4e0d-9b92-d627ece8f037

import Definitions.Def_Submission_ThreeSum_TernaryEuler
import Definitions.Def_Submission_ThreeSum_TernaryTransform
import Theorems.Thm_ThreeSum_TernaryTransform_partial_empty
import Theorems.Thm_ThreeSum_TernaryTransform_coordinateZeta_partial
import Theorems.Thm_ThreeSum_TernaryBank_mem_bank
import Theorems.Thm_ThreeSum_TernaryBank_mem_lowerWords
import Theorems.Thm_ThreeSum_TernaryBank_mem_nearWords
attribute [local simp] ThreeSum.TernaryBank.mem_bank
attribute [local simp] ThreeSum.TernaryBank.mem_lowerWords
attribute [local simp] ThreeSum.TernaryBank.mem_nearWords



set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryTransform
open Finset
open ThreeSum.TernaryJointType ThreeSum.TernaryQuery ThreeSum.TernaryEuler
namespace ThreeSum.TernaryTransform
theorem _root_.solution {N : ℕ} (coords : List (Fin N)) (h : coords.Nodup)
    (f : TritWord N → ℤ) : runZeta coords f = stageSum coords.toFinset f := by
  induction coords with
  | nil => simpa [runZeta] using (partial_empty f).symm
  | cons i rest ih =>
      obtain ⟨hi, hn⟩ := List.nodup_cons.mp h
      rw [runZeta, ih hn, List.toFinset_cons]
      exact coordinateZeta_partial rest.toFinset i (by simpa using hi) f
end ThreeSum.TernaryTransform
