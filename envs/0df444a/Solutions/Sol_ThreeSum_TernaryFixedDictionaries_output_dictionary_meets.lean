-- Prove2me | solution 1 for ThreeSum.TernaryFixedDictionaries.output_dictionary_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:43:11.234202+00:00
-- url     : https://prove2.me/submissions/fbbb4bda-f1d1-4052-b68c-dfca7a143e29

import Definitions.Def_Submission_ThreeSum_TernaryGlobalEncoding
import Definitions.Def_Submission_ThreeSum_LightFixedRadixDictionary
import Definitions.Def_Submission_ThreeSum_TernaryFixedDictionaries
import Theorems.Thm_ThreeSum_TernaryFixedDictionaries_outputKey_abs_bound
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
    (hbase : base+(outputRecords L π I).length ≤ dst)
    (hm : 0 < (outputRecords L π I).length)
    (hspace : LightRadixKeys.space dst (outputRecords L π I).length J ≤ lim.space)
    (hword : (LightRadixKeys.word p ((2*L+2)*p) J : ℤ) ≤ lim.word)
    (hd : d+J+3 ≤ lim.depth) :
    Meets lim (LightFixedRadixDictionary.program ((outputRecords L π I).map (blockKey maps)))
      4 d [base,dst,J,p] μ (LightFixedRadixDictionary.time ((outputRecords L π I).map (blockKey maps)) J)
      (fun r ν => r=((dst+LightRadixKeys.offset (outputRecords L π I).length J : ℕ) : ℤ) ∧
        ν (dst+LightRadixKeys.offset (outputRecords L π I).length J)=
          (((outputRecords L π I).length^J : ℕ) : ℤ) ∧
        Seg ν (dst+LightRadixKeys.offset (outputRecords L π I).length J+1)
          ((tuples (outputRecords L π I) J).map (Radix.positionalHash (p : ℤ) (blockKey maps))) ∧
        Kept μ ν base) :=
  LightFixedRadixDictionary.program_meets_records (outputRecords L π I) (blockKey maps) μ hw hbase hm
    (fun r _ => outputKey_abs_bound maps r) hspace hword hd
end ThreeSum.TernaryFixedDictionaries
