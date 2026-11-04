-- Prove2me | solution 1 for ThreeSum.TernaryFixedDictionaries.trimmed_left_dictionary_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:43:12.391272+00:00
-- url     : https://prove2.me/submissions/5e4a8317-acab-4ebe-99a7-8feba4c44ca3

import Definitions.Def_Submission_ThreeSum_TernaryGlobalEncoding
import Definitions.Def_Submission_ThreeSum_LightFixedRadixDictionary
import Definitions.Def_Submission_ThreeSum_TernaryFixedDictionaries
import Theorems.Thm_ThreeSum_TernaryFixedDictionaries_leftKey_abs_bound
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
    (hbase : base+(trimmedLeftRecords (α := α) maps B).length ≤ dst)
    (hm : 0 < (trimmedLeftRecords (α := α) maps B).length)
    (hspace : LightRadixKeys.space dst (trimmedLeftRecords (α := α) maps B).length J ≤ lim.space)
    (hword : (LightRadixKeys.word p ((2*L+1)*p) J : ℤ) ≤ lim.word)
    (hd : d+J+3 ≤ lim.depth) :
    Meets lim (LightFixedRadixDictionary.program ((trimmedLeftRecords (α := α) maps B).map (leftKey maps)))
      4 d [base,dst,J,p] μ (LightFixedRadixDictionary.time ((trimmedLeftRecords (α := α) maps B).map (leftKey maps)) J)
      (fun r ν => r=((dst+LightRadixKeys.offset (trimmedLeftRecords (α := α) maps B).length J : ℕ) : ℤ) ∧
        ν (dst+LightRadixKeys.offset (trimmedLeftRecords (α := α) maps B).length J)=
          (((trimmedLeftRecords (α := α) maps B).length^J : ℕ) : ℤ) ∧
        Seg ν (dst+LightRadixKeys.offset (trimmedLeftRecords (α := α) maps B).length J+1)
          ((tuples (trimmedLeftRecords (α := α) maps B) J).map (Radix.positionalHash (p : ℤ) (leftKey maps))) ∧
        Kept μ ν base) :=
  LightFixedRadixDictionary.program_meets_records (trimmedLeftRecords (α := α) maps B) (leftKey maps) μ hw hbase hm
    (fun r _ => leftKey_abs_bound maps r) hspace hword hd
end ThreeSum.TernaryFixedDictionaries
