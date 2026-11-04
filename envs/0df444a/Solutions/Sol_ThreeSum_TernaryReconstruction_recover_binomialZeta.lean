-- Prove2me | solution 1 for ThreeSum.TernaryReconstruction.recover_binomialZeta
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:14:52.53145+00:00
-- url     : https://prove2.me/submissions/26d84568-87a1-4aac-8193-332a51fe16ec

import Definitions.Def_Submission_ThreeSum_TernaryEuler
import Definitions.Def_Submission_ThreeSum_TernaryReconstruction
import Theorems.Thm_ThreeSum_TernaryReconstruction_recover_eq
import Theorems.Thm_ThreeSum_TernaryEuler_binomialZeta_euler


set_option autoImplicit false
open ThreeSum ThreeSum.TernaryReconstruction
open Finset
open ThreeSum.TernaryJointType ThreeSum.TernaryBank
open ThreeSum.TernaryQuery ThreeSum.TernaryEuler
namespace ThreeSum.TernaryReconstruction
theorem _root_.solution {N h T : ℕ} (hcut : h ≤ T)
    (f seed : TritWord N → ℤ) (hf : ∀ A, f A ≠ 0 → rank A = h)
    (hbank : ∀ R ∈ bank N T, seed R = binomialZeta f R) (R : TritWord N) :
    recover seed h T (rank R - T) R = binomialZeta f R := by
  apply recover_eq hcut seed (binomialZeta f) hbank (binomialZeta_euler f h hf)
  omega
end ThreeSum.TernaryReconstruction
