-- Prove2me | solution 1 for ThreeSum.TernaryWantedBatchProvenance.decode_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:58:27.306845+00:00
-- url     : https://prove2.me/submissions/529608fc-9197-4967-993f-1f9e59604013

import Definitions.Def_Submission_ThreeSum_TernaryWantedBatchIndex
import Mathlib.Data.List.NodupEquivFin
import Definitions.Def_Submission_ThreeSum_TernaryWantedBatchProvenance
import Theorems.Thm_ThreeSum_TernaryWantedBatchProvenance_descriptors_nodup

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryWantedBatchProvenance
open TernaryWantedRadix TernaryWantedLittleEndian
namespace ThreeSum.TernaryWantedBatchProvenance
theorem _root_.solution (P R S J : ℕ) (raws : List ℤ) (words maps : List ℕ)
    (targets : ℕ→ℤ) (positions : ℕ→ℕ) (n : ℕ) :
    Function.Injective (decode P R S J raws words maps targets positions n) := by
  intro i j he
  apply Fin.ext
  exact congrArg (fun t : Fin (descriptors P J raws targets n).length => t.val)
    ((descriptors_nodup P J raws targets n).injective_get he)
end ThreeSum.TernaryWantedBatchProvenance
