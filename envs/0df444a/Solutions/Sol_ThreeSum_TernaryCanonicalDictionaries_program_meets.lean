-- Prove2me | solution 1 for ThreeSum.TernaryCanonicalDictionaries.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:28:37.778953+00:00
-- url     : https://prove2.me/submissions/cc5cb8cf-61eb-4562-a0c9-6cde410f34ff

import Definitions.Def_Submission_ThreeSum_TernaryFixedDictionaries
import Definitions.Def_Submission_ThreeSum_LightTernaryParallelDictionaries
import Definitions.Def_Submission_ThreeSum_TernaryWantedLittleEndian
import Definitions.Def_Submission_ThreeSum_TernaryBankEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryCanonicalDictionaries
import Theorems.Thm_ThreeSum_TernaryCanonicalDictionaries_native_bound
import Theorems.Thm_ThreeSum_TernaryCanonicalDictionaries_wordCode_bound
import Theorems.Thm_ThreeSum_TernaryCanonicalDictionaries_mapCode_bound
import Theorems.Thm_ThreeSum_LightFixedRadixDictionary_program_meets_records
import Theorems.Thm_ThreeSum_LightTernaryParallelDictionaries_program_meets_records


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryCanonicalDictionaries
open Finset Light RadixKeyLists TernaryFixedDictionaries TernaryJointType
variable {L p : ℕ} [Fact p.Prime] {α : DigitType}
variable {I : Type*} [Fintype I] [DecidableEq I]
variable {lim : Limits}
namespace ThreeSum.TernaryCanonicalDictionaries
theorem _root_.solution (right : Bool)
    (maps : I → TernaryCoverHashes.Coordinate (Fin L) → ZMod p) (B : ℕ)
    {base0 dst0 base1 dst1 base2 dst2 J d : ℕ} (μ : ℕ → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hbase0 : base0+(records (α := α) right maps B).length ≤ dst0)
    (hnext0 : LightRadixKeys.space dst0 (records (α := α) right maps B).length J ≤ base1)
    (hbase1 : base1+(records (α := α) right maps B).length ≤ dst1)
    (hnext1 : LightRadixKeys.space dst1 (records (α := α) right maps B).length J ≤ base2)
    (hbase2 : base2+(records (α := α) right maps B).length ≤ dst2)
    (hspace2 : LightRadixKeys.space dst2 (records (α := α) right maps B).length J ≤ lim.space)
    (hm : 0 < (records (α := α) right maps B).length)
    (hw0 : (LightRadixKeys.word p p J : ℤ) ≤ lim.word)
    (hw1 : (LightRadixKeys.word (4^L) (4^L) J : ℤ) ≤ lim.word)
    (hw2 : (LightRadixKeys.word (Fintype.card I) (Fintype.card I) J : ℤ) ≤ lim.word)
    (hd : d+J+4 ≤ lim.depth) :
    let rs := records (α := α) right maps B
    Meets lim (LightTernaryParallelDictionaries.program
      (rs.map (native right maps)) (rs.map wordCode) (rs.map mapCode)) 15 d
      [base0,dst0,base1,dst1,base2,dst2,J,p,4^L,Fintype.card I] μ
      (LightTernaryParallelDictionaries.time
        (rs.map (native right maps)) (rs.map wordCode) (rs.map mapCode) J)
      (fun r ν => r=((dst2+LightRadixKeys.offset rs.length J : ℕ) : ℤ) ∧
        LightTernaryParallelDictionaries.recordOutput ν dst0 rs (native right maps) p J ∧
        LightTernaryParallelDictionaries.recordOutput ν dst1 rs wordCode (4^L) J ∧
        LightTernaryParallelDictionaries.recordOutput ν dst2 rs mapCode (Fintype.card I) J ∧
        Kept μ ν base0) := by
  apply LightTernaryParallelDictionaries.program_meets_records
    (records (α := α) right maps B) (native right maps) wordCode mapCode μ hw
    hbase0 hnext0 hbase1 hnext1 hbase2 hspace2 hm
    (fun r _ => native_bound right maps r) (fun r _ => wordCode_bound r)
    (fun r _ => mapCode_bound r) hw0 hw1 hw2 hd
end ThreeSum.TernaryCanonicalDictionaries
