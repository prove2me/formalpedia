-- Prove2me | solution 1 for ThreeSum.TernaryWantedBatchProvenance.decode_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:45:43.497529+00:00
-- url     : https://prove2.me/submissions/ee809526-f2d2-4935-a20d-61a014ff81db

import Definitions.Def_Submission_ThreeSum_TernaryWantedBatchIndex
import Mathlib.Data.List.NodupEquivFin
import Definitions.Def_Submission_ThreeSum_TernaryWantedBatchProvenance
import Theorems.Thm_ThreeSum_TernaryWantedBatchIndex_get_mem


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryWantedBatchProvenance
open TernaryWantedRadix TernaryWantedLittleEndian
namespace ThreeSum.TernaryWantedBatchProvenance
theorem _root_.solution (P R S J : ℕ) (raws : List ℤ) (words maps : List ℕ)
    (targets : ℕ→ℤ) (positions : ℕ→ℕ) (n : ℕ) (j) :
    decode P R S J raws words maps targets positions n j∈descriptors P J raws targets n :=
  List.get_mem _ _
end ThreeSum.TernaryWantedBatchProvenance
