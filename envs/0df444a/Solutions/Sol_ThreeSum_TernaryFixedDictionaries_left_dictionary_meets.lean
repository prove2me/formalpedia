-- Prove2me | solution 1 for ThreeSum.TernaryFixedDictionaries.left_dictionary_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:43:08.870278+00:00
-- url     : https://prove2.me/submissions/6fd7e5c7-6c39-4136-bcb7-0a762831b717

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
    {base dst J d : ℕ} (μ : ℕ → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hbase : base+(sourceRecords L α I).length ≤ dst)
    (hm : 0 < (sourceRecords L α I).length)
    (hspace : LightRadixKeys.space dst (sourceRecords L α I).length J ≤ lim.space)
    (hword : (LightRadixKeys.word p ((2*L+1)*p) J : ℤ) ≤ lim.word)
    (hd : d+J+3 ≤ lim.depth) :
    Meets lim (LightFixedRadixDictionary.program ((sourceRecords L α I).map (leftKey maps)))
      4 d [base,dst,J,p] μ (LightFixedRadixDictionary.time ((sourceRecords L α I).map (leftKey maps)) J)
      (fun r ν => r=((dst+LightRadixKeys.offset (sourceRecords L α I).length J : ℕ) : ℤ) ∧
        ν (dst+LightRadixKeys.offset (sourceRecords L α I).length J)=
          (((sourceRecords L α I).length^J : ℕ) : ℤ) ∧
        Seg ν (dst+LightRadixKeys.offset (sourceRecords L α I).length J+1)
          ((tuples (sourceRecords L α I) J).map (Radix.positionalHash (p : ℤ) (leftKey maps))) ∧
        Kept μ ν base) :=
  LightFixedRadixDictionary.program_meets_records (sourceRecords L α I) (leftKey maps) μ hw hbase hm
    (fun r _ => leftKey_abs_bound maps r) hspace hword hd
end ThreeSum.TernaryFixedDictionaries
