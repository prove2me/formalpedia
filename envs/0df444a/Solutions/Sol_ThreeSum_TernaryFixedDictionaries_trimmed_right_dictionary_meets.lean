-- Prove2me | solution 1 for ThreeSum.TernaryFixedDictionaries.trimmed_right_dictionary_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:43:13.530482+00:00
-- url     : https://prove2.me/submissions/c2c64224-9fa6-407c-b6f9-8dae3dfb6b5a

import Definitions.Def_Submission_ThreeSum_TernaryGlobalEncoding
import Definitions.Def_Submission_ThreeSum_LightFixedRadixDictionary
import Definitions.Def_Submission_ThreeSum_TernaryFixedDictionaries
import Theorems.Thm_ThreeSum_TernaryFixedDictionaries_rightKey_abs_bound
import Theorems.Thm_ThreeSum_LightFixedRadixDictionary_program_meets_records


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryFixedDictionaries
open Finset TernaryJointType TernaryCoverLocal TernaryGlobalEncoding RadixKeyLists Light
variable {L p : ℕ} [Fact p.Prime] {α π : DigitType}
variable {I : Type*} [Fintype I] [DecidableEq I]
variable {lim : Limits}
namespace ThreeSum.TernaryFixedDictionaries
theorem _root_.solution (maps : I → TernaryCoverHashes.Coordinate (Fin L) → ZMod p)
    (B : ℕ) {base dst J d : ℕ} (μ : ℕ → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hbase : base+(trimmedRightRecords (α := α) maps B).length ≤ dst)
    (hm : 0 < (trimmedRightRecords (α := α) maps B).length)
    (hspace : LightRadixKeys.space dst (trimmedRightRecords (α := α) maps B).length J ≤ lim.space)
    (hword : (LightRadixKeys.word p ((2*L+1)*p) J : ℤ) ≤ lim.word)
    (hd : d+J+3 ≤ lim.depth) :
    Meets lim (LightFixedRadixDictionary.program ((trimmedRightRecords (α := α) maps B).map (rightKey maps)))
      4 d [base,dst,J,p] μ (LightFixedRadixDictionary.time ((trimmedRightRecords (α := α) maps B).map (rightKey maps)) J)
      (fun r ν => r=((dst+LightRadixKeys.offset (trimmedRightRecords (α := α) maps B).length J : ℕ) : ℤ) ∧
        ν (dst+LightRadixKeys.offset (trimmedRightRecords (α := α) maps B).length J)=
          (((trimmedRightRecords (α := α) maps B).length^J : ℕ) : ℤ) ∧
        Seg ν (dst+LightRadixKeys.offset (trimmedRightRecords (α := α) maps B).length J+1)
          ((tuples (trimmedRightRecords (α := α) maps B) J).map (Radix.positionalHash (p : ℤ) (rightKey maps))) ∧
        Kept μ ν base) :=
  LightFixedRadixDictionary.program_meets_records (trimmedRightRecords (α := α) maps B) (rightKey maps) μ hw hbase hm
    (fun r _ => rightKey_abs_bound maps r) hspace hword hd
end ThreeSum.TernaryFixedDictionaries
