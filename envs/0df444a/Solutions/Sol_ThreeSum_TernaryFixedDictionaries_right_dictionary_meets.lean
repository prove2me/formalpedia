-- Prove2me | solution 1 for ThreeSum.TernaryFixedDictionaries.right_dictionary_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:43:10.081197+00:00
-- url     : https://prove2.me/submissions/f5c7fd9d-d8f8-4e6c-b93b-d69aff8f4437

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
    {base dst J d : ℕ} (μ : ℕ → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hbase : base+(sourceRecords L α I).length ≤ dst)
    (hm : 0 < (sourceRecords L α I).length)
    (hspace : LightRadixKeys.space dst (sourceRecords L α I).length J ≤ lim.space)
    (hword : (LightRadixKeys.word p ((2*L+1)*p) J : ℤ) ≤ lim.word)
    (hd : d+J+3 ≤ lim.depth) :
    Meets lim (LightFixedRadixDictionary.program ((sourceRecords L α I).map (rightKey maps)))
      4 d [base,dst,J,p] μ (LightFixedRadixDictionary.time ((sourceRecords L α I).map (rightKey maps)) J)
      (fun r ν => r=((dst+LightRadixKeys.offset (sourceRecords L α I).length J : ℕ) : ℤ) ∧
        ν (dst+LightRadixKeys.offset (sourceRecords L α I).length J)=
          (((sourceRecords L α I).length^J : ℕ) : ℤ) ∧
        Seg ν (dst+LightRadixKeys.offset (sourceRecords L α I).length J+1)
          ((tuples (sourceRecords L α I) J).map (Radix.positionalHash (p : ℤ) (rightKey maps))) ∧
        Kept μ ν base) :=
  LightFixedRadixDictionary.program_meets_records (sourceRecords L α I) (rightKey maps) μ hw hbase hm
    (fun r _ => rightKey_abs_bound maps r) hspace hword hd
end ThreeSum.TernaryFixedDictionaries
