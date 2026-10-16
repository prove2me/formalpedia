-- Prove2me | solution 1 for TaoFivePrimes.rh_batch01_height_contour_actual_input_upper_zero_k02
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T22:46:57.214845+00:00
-- url     : https://prove2.me/submissions/66aad65a-cfb0-42a9-b9d8-04827330c33c

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighContourVector
import Definitions.Def_TaoFivePrimes_RHHighFFTArithmeticBase
import Definitions.Def_TaoFivePrimes_RHBatch01ContourInputRUpperZeroK02
import Definitions.Def_TaoFivePrimes_RHBatch01ContourInputIUpperZeroK02
import Definitions.Def_TaoFivePrimes_RHBatch01ContourSpectrumUpperZeroK02
namespace RHBatch01SparseSliceRHBatch01ContourActualInputUpperZeroK02B00
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace RHBatch01SequentialContourInput
noncomputable def check (v : List Nat) (start : Nat) : List Nat→List Nat→Bool
  | [],[] => true
  | r::rs,i::is => decide (RHHighContourVector.raw v RHHighFFTArithmeticBase.chirp start=
      ((r:Int)-2^166,(i:Int)-2^166) ∧ r≤2^167 ∧ i≤2^167) && check v (start+1) rs is
  | _,_ => false
lemma sound (v rs is : List Nat) (start j : Nat) (hj:j< rs.length)
    (h:check v start rs is=true) :
    RHHighContourVector.raw v RHHighFFTArithmeticBase.chirp (start+j)=
      ((((rs[j]?).getD 0:Nat):Int)-2^166,(((is[j]?).getD 0:Nat):Int)-2^166) ∧
      ((rs[j]?).getD 0)≤2^167 ∧ ((is[j]?).getD 0)≤2^167 := by
  induction rs generalizing start j is with
  | nil => simp at hj
  | cons r rs ih =>
    cases is with
    | nil => simp [check] at h
    | cons i is =>
      simp only [check,Bool.and_eq_true,decide_eq_true_eq] at h
      cases j with
      | zero => simpa only [Nat.add_zero,List.getElem?_cons_zero,Option.getD_some] using h.1
      | succ j =>
        have hh:=ih is (start+1) j (by simpa using hj) h.2
        simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,List.getElem?_cons_succ] using hh
end RHBatch01SequentialContourInput
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
open RHBatch01SequentialContourInput
noncomputable def v : List Nat := RHBatch01ContourSpectrumUpperZeroK02.rows.flatten
noncomputable def rr (c : Nat) : List Nat := (((RHBatch01ContourInputRUpperZeroK02.rows[0]?).getD []).drop (16*c)).take 16
noncomputable def ii (c : Nat) : List Nat := (((RHBatch01ContourInputIUpperZeroK02.rows[0]?).getD []).drop (16*c)).take 16
theorem checked00 : check v 0
 ((RHBatch01ContourInputRUpperZeroK02.row00.drop 0).take 16) ((RHBatch01ContourInputIUpperZeroK02.row00.drop 0).take 16)=true ∧
 ((RHBatch01ContourInputRUpperZeroK02.row00.drop 0).take 16).length=16 := by decide +kernel
theorem checked01 : check v 16
 ((RHBatch01ContourInputRUpperZeroK02.row00.drop 16).take 16) ((RHBatch01ContourInputIUpperZeroK02.row00.drop 16).take 16)=true ∧
 ((RHBatch01ContourInputRUpperZeroK02.row00.drop 16).take 16).length=16 := by decide +kernel
theorem checked02 : check v 32
 ((RHBatch01ContourInputRUpperZeroK02.row00.drop 32).take 16) ((RHBatch01ContourInputIUpperZeroK02.row00.drop 32).take 16)=true ∧
 ((RHBatch01ContourInputRUpperZeroK02.row00.drop 32).take 16).length=16 := by decide +kernel
theorem checked03 : check v 48
 ((RHBatch01ContourInputRUpperZeroK02.row00.drop 48).take 16) ((RHBatch01ContourInputIUpperZeroK02.row00.drop 48).take 16)=true ∧
 ((RHBatch01ContourInputRUpperZeroK02.row00.drop 48).take 16).length=16 := by decide +kernel
theorem checked04 : check v 64
 ((RHBatch01ContourInputRUpperZeroK02.row00.drop 64).take 16) ((RHBatch01ContourInputIUpperZeroK02.row00.drop 64).take 16)=true ∧
 ((RHBatch01ContourInputRUpperZeroK02.row00.drop 64).take 16).length=16 := by decide +kernel
theorem checked05 : check v 80
 ((RHBatch01ContourInputRUpperZeroK02.row00.drop 80).take 16) ((RHBatch01ContourInputIUpperZeroK02.row00.drop 80).take 16)=true ∧
 ((RHBatch01ContourInputRUpperZeroK02.row00.drop 80).take 16).length=16 := by decide +kernel
theorem checked06 : check v 96
 ((RHBatch01ContourInputRUpperZeroK02.row00.drop 96).take 16) ((RHBatch01ContourInputIUpperZeroK02.row00.drop 96).take 16)=true ∧
 ((RHBatch01ContourInputRUpperZeroK02.row00.drop 96).take 16).length=16 := by decide +kernel
theorem checked07 : check v 112
 ((RHBatch01ContourInputRUpperZeroK02.row00.drop 112).take 16) ((RHBatch01ContourInputIUpperZeroK02.row00.drop 112).take 16)=true ∧
 ((RHBatch01ContourInputRUpperZeroK02.row00.drop 112).take 16).length=16 := by decide +kernel
theorem checked08 : check v 128
 ((RHBatch01ContourInputRUpperZeroK02.row00.drop 128).take 16) ((RHBatch01ContourInputIUpperZeroK02.row00.drop 128).take 16)=true ∧
 ((RHBatch01ContourInputRUpperZeroK02.row00.drop 128).take 16).length=16 := by decide +kernel
theorem checked09 : check v 144
 ((RHBatch01ContourInputRUpperZeroK02.row00.drop 144).take 16) ((RHBatch01ContourInputIUpperZeroK02.row00.drop 144).take 16)=true ∧
 ((RHBatch01ContourInputRUpperZeroK02.row00.drop 144).take 16).length=16 := by decide +kernel
theorem checked10 : check v 160
 ((RHBatch01ContourInputRUpperZeroK02.row00.drop 160).take 16) ((RHBatch01ContourInputIUpperZeroK02.row00.drop 160).take 16)=true ∧
 ((RHBatch01ContourInputRUpperZeroK02.row00.drop 160).take 16).length=16 := by decide +kernel
theorem checked11 : check v 176
 ((RHBatch01ContourInputRUpperZeroK02.row00.drop 176).take 16) ((RHBatch01ContourInputIUpperZeroK02.row00.drop 176).take 16)=true ∧
 ((RHBatch01ContourInputRUpperZeroK02.row00.drop 176).take 16).length=16 := by decide +kernel
theorem checked12 : check v 192
 ((RHBatch01ContourInputRUpperZeroK02.row00.drop 192).take 16) ((RHBatch01ContourInputIUpperZeroK02.row00.drop 192).take 16)=true ∧
 ((RHBatch01ContourInputRUpperZeroK02.row00.drop 192).take 16).length=16 := by decide +kernel
theorem checked13 : check v 208
 ((RHBatch01ContourInputRUpperZeroK02.row00.drop 208).take 16) ((RHBatch01ContourInputIUpperZeroK02.row00.drop 208).take 16)=true ∧
 ((RHBatch01ContourInputRUpperZeroK02.row00.drop 208).take 16).length=16 := by decide +kernel
theorem checked14 : check v 224
 ((RHBatch01ContourInputRUpperZeroK02.row00.drop 224).take 16) ((RHBatch01ContourInputIUpperZeroK02.row00.drop 224).take 16)=true ∧
 ((RHBatch01ContourInputRUpperZeroK02.row00.drop 224).take 16).length=16 := by decide +kernel
theorem checked15 : check v 240
 ((RHBatch01ContourInputRUpperZeroK02.row00.drop 240).take 16) ((RHBatch01ContourInputIUpperZeroK02.row00.drop 240).take 16)=true ∧
 ((RHBatch01ContourInputRUpperZeroK02.row00.drop 240).take 16).length=16 := by decide +kernel
theorem checked16 : check v 256
 ((RHBatch01ContourInputRUpperZeroK02.row00.drop 256).take 16) ((RHBatch01ContourInputIUpperZeroK02.row00.drop 256).take 16)=true ∧
 ((RHBatch01ContourInputRUpperZeroK02.row00.drop 256).take 16).length=16 := by decide +kernel
theorem checked17 : check v 272
 ((RHBatch01ContourInputRUpperZeroK02.row00.drop 272).take 16) ((RHBatch01ContourInputIUpperZeroK02.row00.drop 272).take 16)=true ∧
 ((RHBatch01ContourInputRUpperZeroK02.row00.drop 272).take 16).length=16 := by decide +kernel
theorem checked18 : check v 288
 ((RHBatch01ContourInputRUpperZeroK02.row00.drop 288).take 16) ((RHBatch01ContourInputIUpperZeroK02.row00.drop 288).take 16)=true ∧
 ((RHBatch01ContourInputRUpperZeroK02.row00.drop 288).take 16).length=16 := by decide +kernel
theorem checked19 : check v 304
 ((RHBatch01ContourInputRUpperZeroK02.row00.drop 304).take 16) ((RHBatch01ContourInputIUpperZeroK02.row00.drop 304).take 16)=true ∧
 ((RHBatch01ContourInputRUpperZeroK02.row00.drop 304).take 16).length=16 := by decide +kernel
theorem checked20 : check v 320
 ((RHBatch01ContourInputRUpperZeroK02.row00.drop 320).take 16) ((RHBatch01ContourInputIUpperZeroK02.row00.drop 320).take 16)=true ∧
 ((RHBatch01ContourInputRUpperZeroK02.row00.drop 320).take 16).length=16 := by decide +kernel
theorem checked21 : check v 336
 ((RHBatch01ContourInputRUpperZeroK02.row00.drop 336).take 16) ((RHBatch01ContourInputIUpperZeroK02.row00.drop 336).take 16)=true ∧
 ((RHBatch01ContourInputRUpperZeroK02.row00.drop 336).take 16).length=16 := by decide +kernel
theorem checked22 : check v 352
 ((RHBatch01ContourInputRUpperZeroK02.row00.drop 352).take 16) ((RHBatch01ContourInputIUpperZeroK02.row00.drop 352).take 16)=true ∧
 ((RHBatch01ContourInputRUpperZeroK02.row00.drop 352).take 16).length=16 := by decide +kernel
theorem checked23 : check v 368
 ((RHBatch01ContourInputRUpperZeroK02.row00.drop 368).take 16) ((RHBatch01ContourInputIUpperZeroK02.row00.drop 368).take 16)=true ∧
 ((RHBatch01ContourInputRUpperZeroK02.row00.drop 368).take 16).length=16 := by decide +kernel
theorem checked24 : check v 384
 ((RHBatch01ContourInputRUpperZeroK02.row00.drop 384).take 16) ((RHBatch01ContourInputIUpperZeroK02.row00.drop 384).take 16)=true ∧
 ((RHBatch01ContourInputRUpperZeroK02.row00.drop 384).take 16).length=16 := by decide +kernel
theorem checked25 : check v 400
 ((RHBatch01ContourInputRUpperZeroK02.row00.drop 400).take 16) ((RHBatch01ContourInputIUpperZeroK02.row00.drop 400).take 16)=true ∧
 ((RHBatch01ContourInputRUpperZeroK02.row00.drop 400).take 16).length=16 := by decide +kernel
theorem checked26 : check v 416
 ((RHBatch01ContourInputRUpperZeroK02.row00.drop 416).take 16) ((RHBatch01ContourInputIUpperZeroK02.row00.drop 416).take 16)=true ∧
 ((RHBatch01ContourInputRUpperZeroK02.row00.drop 416).take 16).length=16 := by decide +kernel
theorem checked27 : check v 432
 ((RHBatch01ContourInputRUpperZeroK02.row00.drop 432).take 16) ((RHBatch01ContourInputIUpperZeroK02.row00.drop 432).take 16)=true ∧
 ((RHBatch01ContourInputRUpperZeroK02.row00.drop 432).take 16).length=16 := by decide +kernel
theorem checked28 : check v 448
 ((RHBatch01ContourInputRUpperZeroK02.row00.drop 448).take 16) ((RHBatch01ContourInputIUpperZeroK02.row00.drop 448).take 16)=true ∧
 ((RHBatch01ContourInputRUpperZeroK02.row00.drop 448).take 16).length=16 := by decide +kernel
theorem checked29 : check v 464
 ((RHBatch01ContourInputRUpperZeroK02.row00.drop 464).take 16) ((RHBatch01ContourInputIUpperZeroK02.row00.drop 464).take 16)=true ∧
 ((RHBatch01ContourInputRUpperZeroK02.row00.drop 464).take 16).length=16 := by decide +kernel
theorem checked30 : check v 480
 ((RHBatch01ContourInputRUpperZeroK02.row00.drop 480).take 16) ((RHBatch01ContourInputIUpperZeroK02.row00.drop 480).take 16)=true ∧
 ((RHBatch01ContourInputRUpperZeroK02.row00.drop 480).take 16).length=16 := by decide +kernel
theorem checked31 : check v 496
 ((RHBatch01ContourInputRUpperZeroK02.row00.drop 496).take 16) ((RHBatch01ContourInputIUpperZeroK02.row00.drop 496).take 16)=true ∧
 ((RHBatch01ContourInputRUpperZeroK02.row00.drop 496).take 16).length=16 := by decide +kernel
lemma all_checked (c : Nat) (hc:c<32) :
 check v (0+16*c) (rr c) (ii c)=true ∧ (rr c).length=16 := by
 interval_cases c
 · exact checked00
 · exact checked01
 · exact checked02
 · exact checked03
 · exact checked04
 · exact checked05
 · exact checked06
 · exact checked07
 · exact checked08
 · exact checked09
 · exact checked10
 · exact checked11
 · exact checked12
 · exact checked13
 · exact checked14
 · exact checked15
 · exact checked16
 · exact checked17
 · exact checked18
 · exact checked19
 · exact checked20
 · exact checked21
 · exact checked22
 · exact checked23
 · exact checked24
 · exact checked25
 · exact checked26
 · exact checked27
 · exact checked28
 · exact checked29
 · exact checked30
 · exact checked31
end RHBatch01SparseSliceRHBatch01ContourActualInputUpperZeroK02B00
theorem TaoFivePrimes.rh_batch01_height_contour_actual_input_upper_zero_k02_slice00 :
 ∀i:Nat,i<512 →
 RHHighContourVector.raw RHBatch01ContourSpectrumUpperZeroK02.rows.flatten RHHighFFTArithmeticBase.chirp (0+i)=
  ((((((RHBatch01ContourInputRUpperZeroK02.rows[0]?).getD [])[i]?).getD 0:Nat):Int)-2^166,
   (((((RHBatch01ContourInputIUpperZeroK02.rows[0]?).getD [])[i]?).getD 0:Nat):Int)-2^166) ∧
  ((((RHBatch01ContourInputRUpperZeroK02.rows[0]?).getD [])[i]?).getD 0)≤2^167 ∧
  ((((RHBatch01ContourInputIUpperZeroK02.rows[0]?).getD [])[i]?).getD 0)≤2^167 := by
 intro i hi
 have h:=RHBatch01SparseSliceRHBatch01ContourActualInputUpperZeroK02B00.all_checked (i/16) (by omega)
 have hh:=RHBatch01SparseSliceRHBatch01ContourActualInputUpperZeroK02B00.RHBatch01SequentialContourInput.sound RHBatch01SparseSliceRHBatch01ContourActualInputUpperZeroK02B00.v (RHBatch01SparseSliceRHBatch01ContourActualInputUpperZeroK02B00.rr (i/16)) (RHBatch01SparseSliceRHBatch01ContourActualInputUpperZeroK02B00.ii (i/16))
  (0+16*(i/16)) (i%16) (by rw[h.2];omega) h.1
 have he:16*(i/16)+i%16=i:=by omega
 simpa only[RHBatch01SparseSliceRHBatch01ContourActualInputUpperZeroK02B00.v,RHBatch01SparseSliceRHBatch01ContourActualInputUpperZeroK02B00.rr,RHBatch01SparseSliceRHBatch01ContourActualInputUpperZeroK02B00.ii,List.getElem?_take,List.getElem?_drop,
  show i%16<16 by omega,if_true,show 0+16*(i/16)+i%16=0+i by omega,he] using hh
namespace RHBatch01SparseSliceRHBatch01ContourActualInputUpperZeroK02B01
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace RHBatch01SequentialContourInput
noncomputable def check (v : List Nat) (start : Nat) : List Nat→List Nat→Bool
  | [],[] => true
  | r::rs,i::is => decide (RHHighContourVector.raw v RHHighFFTArithmeticBase.chirp start=
      ((r:Int)-2^166,(i:Int)-2^166) ∧ r≤2^167 ∧ i≤2^167) && check v (start+1) rs is
  | _,_ => false
lemma sound (v rs is : List Nat) (start j : Nat) (hj:j< rs.length)
    (h:check v start rs is=true) :
    RHHighContourVector.raw v RHHighFFTArithmeticBase.chirp (start+j)=
      ((((rs[j]?).getD 0:Nat):Int)-2^166,(((is[j]?).getD 0:Nat):Int)-2^166) ∧
      ((rs[j]?).getD 0)≤2^167 ∧ ((is[j]?).getD 0)≤2^167 := by
  induction rs generalizing start j is with
  | nil => simp at hj
  | cons r rs ih =>
    cases is with
    | nil => simp [check] at h
    | cons i is =>
      simp only [check,Bool.and_eq_true,decide_eq_true_eq] at h
      cases j with
      | zero => simpa only [Nat.add_zero,List.getElem?_cons_zero,Option.getD_some] using h.1
      | succ j =>
        have hh:=ih is (start+1) j (by simpa using hj) h.2
        simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,List.getElem?_cons_succ] using hh
end RHBatch01SequentialContourInput
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
open RHBatch01SequentialContourInput
noncomputable def v : List Nat := RHBatch01ContourSpectrumUpperZeroK02.rows.flatten
noncomputable def rr (c : Nat) : List Nat := (((RHBatch01ContourInputRUpperZeroK02.rows[1]?).getD []).drop (16*c)).take 16
noncomputable def ii (c : Nat) : List Nat := (((RHBatch01ContourInputIUpperZeroK02.rows[1]?).getD []).drop (16*c)).take 16
theorem checked00 : check v 512
 ((RHBatch01ContourInputRUpperZeroK02.row01.drop 0).take 16) ((RHBatch01ContourInputIUpperZeroK02.row01.drop 0).take 16)=true ∧
 ((RHBatch01ContourInputRUpperZeroK02.row01.drop 0).take 16).length=16 := by decide +kernel
theorem checked01 : check v 528
 ((RHBatch01ContourInputRUpperZeroK02.row01.drop 16).take 16) ((RHBatch01ContourInputIUpperZeroK02.row01.drop 16).take 16)=true ∧
 ((RHBatch01ContourInputRUpperZeroK02.row01.drop 16).take 16).length=16 := by decide +kernel
theorem checked02 : check v 544
 ((RHBatch01ContourInputRUpperZeroK02.row01.drop 32).take 16) ((RHBatch01ContourInputIUpperZeroK02.row01.drop 32).take 16)=true ∧
 ((RHBatch01ContourInputRUpperZeroK02.row01.drop 32).take 16).length=16 := by decide +kernel
theorem checked03 : check v 560
 ((RHBatch01ContourInputRUpperZeroK02.row01.drop 48).take 16) ((RHBatch01ContourInputIUpperZeroK02.row01.drop 48).take 16)=true ∧
 ((RHBatch01ContourInputRUpperZeroK02.row01.drop 48).take 16).length=16 := by decide +kernel
theorem checked04 : check v 576
 ((RHBatch01ContourInputRUpperZeroK02.row01.drop 64).take 16) ((RHBatch01ContourInputIUpperZeroK02.row01.drop 64).take 16)=true ∧
 ((RHBatch01ContourInputRUpperZeroK02.row01.drop 64).take 16).length=16 := by decide +kernel
theorem checked05 : check v 592
 ((RHBatch01ContourInputRUpperZeroK02.row01.drop 80).take 16) ((RHBatch01ContourInputIUpperZeroK02.row01.drop 80).take 16)=true ∧
 ((RHBatch01ContourInputRUpperZeroK02.row01.drop 80).take 16).length=16 := by decide +kernel
theorem checked06 : check v 608
 ((RHBatch01ContourInputRUpperZeroK02.row01.drop 96).take 16) ((RHBatch01ContourInputIUpperZeroK02.row01.drop 96).take 16)=true ∧
 ((RHBatch01ContourInputRUpperZeroK02.row01.drop 96).take 16).length=16 := by decide +kernel
theorem checked07 : check v 624
 ((RHBatch01ContourInputRUpperZeroK02.row01.drop 112).take 16) ((RHBatch01ContourInputIUpperZeroK02.row01.drop 112).take 16)=true ∧
 ((RHBatch01ContourInputRUpperZeroK02.row01.drop 112).take 16).length=16 := by decide +kernel
theorem checked08 : check v 640
 ((RHBatch01ContourInputRUpperZeroK02.row01.drop 128).take 16) ((RHBatch01ContourInputIUpperZeroK02.row01.drop 128).take 16)=true ∧
 ((RHBatch01ContourInputRUpperZeroK02.row01.drop 128).take 16).length=16 := by decide +kernel
theorem checked09 : check v 656
 ((RHBatch01ContourInputRUpperZeroK02.row01.drop 144).take 16) ((RHBatch01ContourInputIUpperZeroK02.row01.drop 144).take 16)=true ∧
 ((RHBatch01ContourInputRUpperZeroK02.row01.drop 144).take 16).length=16 := by decide +kernel
theorem checked10 : check v 672
 ((RHBatch01ContourInputRUpperZeroK02.row01.drop 160).take 16) ((RHBatch01ContourInputIUpperZeroK02.row01.drop 160).take 16)=true ∧
 ((RHBatch01ContourInputRUpperZeroK02.row01.drop 160).take 16).length=16 := by decide +kernel
theorem checked11 : check v 688
 ((RHBatch01ContourInputRUpperZeroK02.row01.drop 176).take 16) ((RHBatch01ContourInputIUpperZeroK02.row01.drop 176).take 16)=true ∧
 ((RHBatch01ContourInputRUpperZeroK02.row01.drop 176).take 16).length=16 := by decide +kernel
theorem checked12 : check v 704
 ((RHBatch01ContourInputRUpperZeroK02.row01.drop 192).take 16) ((RHBatch01ContourInputIUpperZeroK02.row01.drop 192).take 16)=true ∧
 ((RHBatch01ContourInputRUpperZeroK02.row01.drop 192).take 16).length=16 := by decide +kernel
theorem checked13 : check v 720
 ((RHBatch01ContourInputRUpperZeroK02.row01.drop 208).take 16) ((RHBatch01ContourInputIUpperZeroK02.row01.drop 208).take 16)=true ∧
 ((RHBatch01ContourInputRUpperZeroK02.row01.drop 208).take 16).length=16 := by decide +kernel
theorem checked14 : check v 736
 ((RHBatch01ContourInputRUpperZeroK02.row01.drop 224).take 16) ((RHBatch01ContourInputIUpperZeroK02.row01.drop 224).take 16)=true ∧
 ((RHBatch01ContourInputRUpperZeroK02.row01.drop 224).take 16).length=16 := by decide +kernel
theorem checked15 : check v 752
 ((RHBatch01ContourInputRUpperZeroK02.row01.drop 240).take 16) ((RHBatch01ContourInputIUpperZeroK02.row01.drop 240).take 16)=true ∧
 ((RHBatch01ContourInputRUpperZeroK02.row01.drop 240).take 16).length=16 := by decide +kernel
theorem checked16 : check v 768
 ((RHBatch01ContourInputRUpperZeroK02.row01.drop 256).take 16) ((RHBatch01ContourInputIUpperZeroK02.row01.drop 256).take 16)=true ∧
 ((RHBatch01ContourInputRUpperZeroK02.row01.drop 256).take 16).length=16 := by decide +kernel
theorem checked17 : check v 784
 ((RHBatch01ContourInputRUpperZeroK02.row01.drop 272).take 16) ((RHBatch01ContourInputIUpperZeroK02.row01.drop 272).take 16)=true ∧
 ((RHBatch01ContourInputRUpperZeroK02.row01.drop 272).take 16).length=16 := by decide +kernel
theorem checked18 : check v 800
 ((RHBatch01ContourInputRUpperZeroK02.row01.drop 288).take 16) ((RHBatch01ContourInputIUpperZeroK02.row01.drop 288).take 16)=true ∧
 ((RHBatch01ContourInputRUpperZeroK02.row01.drop 288).take 16).length=16 := by decide +kernel
theorem checked19 : check v 816
 ((RHBatch01ContourInputRUpperZeroK02.row01.drop 304).take 16) ((RHBatch01ContourInputIUpperZeroK02.row01.drop 304).take 16)=true ∧
 ((RHBatch01ContourInputRUpperZeroK02.row01.drop 304).take 16).length=16 := by decide +kernel
theorem checked20 : check v 832
 ((RHBatch01ContourInputRUpperZeroK02.row01.drop 320).take 16) ((RHBatch01ContourInputIUpperZeroK02.row01.drop 320).take 16)=true ∧
 ((RHBatch01ContourInputRUpperZeroK02.row01.drop 320).take 16).length=16 := by decide +kernel
theorem checked21 : check v 848
 ((RHBatch01ContourInputRUpperZeroK02.row01.drop 336).take 16) ((RHBatch01ContourInputIUpperZeroK02.row01.drop 336).take 16)=true ∧
 ((RHBatch01ContourInputRUpperZeroK02.row01.drop 336).take 16).length=16 := by decide +kernel
theorem checked22 : check v 864
 ((RHBatch01ContourInputRUpperZeroK02.row01.drop 352).take 16) ((RHBatch01ContourInputIUpperZeroK02.row01.drop 352).take 16)=true ∧
 ((RHBatch01ContourInputRUpperZeroK02.row01.drop 352).take 16).length=16 := by decide +kernel
theorem checked23 : check v 880
 ((RHBatch01ContourInputRUpperZeroK02.row01.drop 368).take 16) ((RHBatch01ContourInputIUpperZeroK02.row01.drop 368).take 16)=true ∧
 ((RHBatch01ContourInputRUpperZeroK02.row01.drop 368).take 16).length=16 := by decide +kernel
theorem checked24 : check v 896
 ((RHBatch01ContourInputRUpperZeroK02.row01.drop 384).take 16) ((RHBatch01ContourInputIUpperZeroK02.row01.drop 384).take 16)=true ∧
 ((RHBatch01ContourInputRUpperZeroK02.row01.drop 384).take 16).length=16 := by decide +kernel
theorem checked25 : check v 912
 ((RHBatch01ContourInputRUpperZeroK02.row01.drop 400).take 16) ((RHBatch01ContourInputIUpperZeroK02.row01.drop 400).take 16)=true ∧
 ((RHBatch01ContourInputRUpperZeroK02.row01.drop 400).take 16).length=16 := by decide +kernel
theorem checked26 : check v 928
 ((RHBatch01ContourInputRUpperZeroK02.row01.drop 416).take 16) ((RHBatch01ContourInputIUpperZeroK02.row01.drop 416).take 16)=true ∧
 ((RHBatch01ContourInputRUpperZeroK02.row01.drop 416).take 16).length=16 := by decide +kernel
theorem checked27 : check v 944
 ((RHBatch01ContourInputRUpperZeroK02.row01.drop 432).take 16) ((RHBatch01ContourInputIUpperZeroK02.row01.drop 432).take 16)=true ∧
 ((RHBatch01ContourInputRUpperZeroK02.row01.drop 432).take 16).length=16 := by decide +kernel
theorem checked28 : check v 960
 ((RHBatch01ContourInputRUpperZeroK02.row01.drop 448).take 16) ((RHBatch01ContourInputIUpperZeroK02.row01.drop 448).take 16)=true ∧
 ((RHBatch01ContourInputRUpperZeroK02.row01.drop 448).take 16).length=16 := by decide +kernel
theorem checked29 : check v 976
 ((RHBatch01ContourInputRUpperZeroK02.row01.drop 464).take 16) ((RHBatch01ContourInputIUpperZeroK02.row01.drop 464).take 16)=true ∧
 ((RHBatch01ContourInputRUpperZeroK02.row01.drop 464).take 16).length=16 := by decide +kernel
theorem checked30 : check v 992
 ((RHBatch01ContourInputRUpperZeroK02.row01.drop 480).take 16) ((RHBatch01ContourInputIUpperZeroK02.row01.drop 480).take 16)=true ∧
 ((RHBatch01ContourInputRUpperZeroK02.row01.drop 480).take 16).length=16 := by decide +kernel
theorem checked31 : check v 1008
 ((RHBatch01ContourInputRUpperZeroK02.row01.drop 496).take 16) ((RHBatch01ContourInputIUpperZeroK02.row01.drop 496).take 16)=true ∧
 ((RHBatch01ContourInputRUpperZeroK02.row01.drop 496).take 16).length=16 := by decide +kernel
lemma all_checked (c : Nat) (hc:c<32) :
 check v (512+16*c) (rr c) (ii c)=true ∧ (rr c).length=16 := by
 interval_cases c
 · exact checked00
 · exact checked01
 · exact checked02
 · exact checked03
 · exact checked04
 · exact checked05
 · exact checked06
 · exact checked07
 · exact checked08
 · exact checked09
 · exact checked10
 · exact checked11
 · exact checked12
 · exact checked13
 · exact checked14
 · exact checked15
 · exact checked16
 · exact checked17
 · exact checked18
 · exact checked19
 · exact checked20
 · exact checked21
 · exact checked22
 · exact checked23
 · exact checked24
 · exact checked25
 · exact checked26
 · exact checked27
 · exact checked28
 · exact checked29
 · exact checked30
 · exact checked31
end RHBatch01SparseSliceRHBatch01ContourActualInputUpperZeroK02B01
theorem TaoFivePrimes.rh_batch01_height_contour_actual_input_upper_zero_k02_slice01 :
 ∀i:Nat,i<512 →
 RHHighContourVector.raw RHBatch01ContourSpectrumUpperZeroK02.rows.flatten RHHighFFTArithmeticBase.chirp (512+i)=
  ((((((RHBatch01ContourInputRUpperZeroK02.rows[1]?).getD [])[i]?).getD 0:Nat):Int)-2^166,
   (((((RHBatch01ContourInputIUpperZeroK02.rows[1]?).getD [])[i]?).getD 0:Nat):Int)-2^166) ∧
  ((((RHBatch01ContourInputRUpperZeroK02.rows[1]?).getD [])[i]?).getD 0)≤2^167 ∧
  ((((RHBatch01ContourInputIUpperZeroK02.rows[1]?).getD [])[i]?).getD 0)≤2^167 := by
 intro i hi
 have h:=RHBatch01SparseSliceRHBatch01ContourActualInputUpperZeroK02B01.all_checked (i/16) (by omega)
 have hh:=RHBatch01SparseSliceRHBatch01ContourActualInputUpperZeroK02B01.RHBatch01SequentialContourInput.sound RHBatch01SparseSliceRHBatch01ContourActualInputUpperZeroK02B01.v (RHBatch01SparseSliceRHBatch01ContourActualInputUpperZeroK02B01.rr (i/16)) (RHBatch01SparseSliceRHBatch01ContourActualInputUpperZeroK02B01.ii (i/16))
  (512+16*(i/16)) (i%16) (by rw[h.2];omega) h.1
 have he:16*(i/16)+i%16=i:=by omega
 simpa only[RHBatch01SparseSliceRHBatch01ContourActualInputUpperZeroK02B01.v,RHBatch01SparseSliceRHBatch01ContourActualInputUpperZeroK02B01.rr,RHBatch01SparseSliceRHBatch01ContourActualInputUpperZeroK02B01.ii,List.getElem?_take,List.getElem?_drop,
  show i%16<16 by omega,if_true,show 512+16*(i/16)+i%16=512+i by omega,he] using hh
namespace RHBatch01SparseSliceRHBatch01ContourActualInputUpperZeroK02B02
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace RHBatch01SequentialContourInput
noncomputable def check (v : List Nat) (start : Nat) : List Nat→List Nat→Bool
  | [],[] => true
  | r::rs,i::is => decide (RHHighContourVector.raw v RHHighFFTArithmeticBase.chirp start=
      ((r:Int)-2^166,(i:Int)-2^166) ∧ r≤2^167 ∧ i≤2^167) && check v (start+1) rs is
  | _,_ => false
lemma sound (v rs is : List Nat) (start j : Nat) (hj:j< rs.length)
    (h:check v start rs is=true) :
    RHHighContourVector.raw v RHHighFFTArithmeticBase.chirp (start+j)=
      ((((rs[j]?).getD 0:Nat):Int)-2^166,(((is[j]?).getD 0:Nat):Int)-2^166) ∧
      ((rs[j]?).getD 0)≤2^167 ∧ ((is[j]?).getD 0)≤2^167 := by
  induction rs generalizing start j is with
  | nil => simp at hj
  | cons r rs ih =>
    cases is with
    | nil => simp [check] at h
    | cons i is =>
      simp only [check,Bool.and_eq_true,decide_eq_true_eq] at h
      cases j with
      | zero => simpa only [Nat.add_zero,List.getElem?_cons_zero,Option.getD_some] using h.1
      | succ j =>
        have hh:=ih is (start+1) j (by simpa using hj) h.2
        simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,List.getElem?_cons_succ] using hh
end RHBatch01SequentialContourInput
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
open RHBatch01SequentialContourInput
noncomputable def v : List Nat := RHBatch01ContourSpectrumUpperZeroK02.rows.flatten
noncomputable def rr (c : Nat) : List Nat := (((RHBatch01ContourInputRUpperZeroK02.rows[2]?).getD []).drop (16*c)).take 1
noncomputable def ii (c : Nat) : List Nat := (((RHBatch01ContourInputIUpperZeroK02.rows[2]?).getD []).drop (16*c)).take 1
theorem checked00 : check v 1024
 ((RHBatch01ContourInputRUpperZeroK02.row02.drop 0).take 1) ((RHBatch01ContourInputIUpperZeroK02.row02.drop 0).take 1)=true ∧
 ((RHBatch01ContourInputRUpperZeroK02.row02.drop 0).take 1).length=1 := by decide +kernel
lemma all_checked (c : Nat) (hc:c<1) :
 check v (1024+16*c) (rr c) (ii c)=true ∧ (rr c).length=1 := by
 interval_cases c
 · exact checked00
end RHBatch01SparseSliceRHBatch01ContourActualInputUpperZeroK02B02
theorem TaoFivePrimes.rh_batch01_height_contour_actual_input_upper_zero_k02_slice02 :
 ∀i:Nat,i<1 →
 RHHighContourVector.raw RHBatch01ContourSpectrumUpperZeroK02.rows.flatten RHHighFFTArithmeticBase.chirp (1024+i)=
  ((((((RHBatch01ContourInputRUpperZeroK02.rows[2]?).getD [])[i]?).getD 0:Nat):Int)-2^166,
   (((((RHBatch01ContourInputIUpperZeroK02.rows[2]?).getD [])[i]?).getD 0:Nat):Int)-2^166) ∧
  ((((RHBatch01ContourInputRUpperZeroK02.rows[2]?).getD [])[i]?).getD 0)≤2^167 ∧
  ((((RHBatch01ContourInputIUpperZeroK02.rows[2]?).getD [])[i]?).getD 0)≤2^167 := by
 intro i hi
 have h:=RHBatch01SparseSliceRHBatch01ContourActualInputUpperZeroK02B02.all_checked (i/16) (by omega)
 have hh:=RHBatch01SparseSliceRHBatch01ContourActualInputUpperZeroK02B02.RHBatch01SequentialContourInput.sound RHBatch01SparseSliceRHBatch01ContourActualInputUpperZeroK02B02.v (RHBatch01SparseSliceRHBatch01ContourActualInputUpperZeroK02B02.rr (i/16)) (RHBatch01SparseSliceRHBatch01ContourActualInputUpperZeroK02B02.ii (i/16))
  (1024+16*(i/16)) (i%16) (by rw[h.2];omega) h.1
 have he:16*(i/16)+i%16=i:=by omega
 simpa only[RHBatch01SparseSliceRHBatch01ContourActualInputUpperZeroK02B02.v,RHBatch01SparseSliceRHBatch01ContourActualInputUpperZeroK02B02.rr,RHBatch01SparseSliceRHBatch01ContourActualInputUpperZeroK02B02.ii,List.getElem?_take,List.getElem?_drop,
  show i%16<1 by omega,if_true,show 1024+16*(i/16)+i%16=1024+i by omega,he] using hh
namespace RHBatch01SparseSliceRHBatch01ContourActualInputUpperZeroK02B30
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace RHBatch01SequentialContourInput
noncomputable def check (v : List Nat) (start : Nat) : List Nat→List Nat→Bool
  | [],[] => true
  | r::rs,i::is => decide (RHHighContourVector.raw v RHHighFFTArithmeticBase.chirp start=
      ((r:Int)-2^166,(i:Int)-2^166) ∧ r≤2^167 ∧ i≤2^167) && check v (start+1) rs is
  | _,_ => false
lemma sound (v rs is : List Nat) (start j : Nat) (hj:j< rs.length)
    (h:check v start rs is=true) :
    RHHighContourVector.raw v RHHighFFTArithmeticBase.chirp (start+j)=
      ((((rs[j]?).getD 0:Nat):Int)-2^166,(((is[j]?).getD 0:Nat):Int)-2^166) ∧
      ((rs[j]?).getD 0)≤2^167 ∧ ((is[j]?).getD 0)≤2^167 := by
  induction rs generalizing start j is with
  | nil => simp at hj
  | cons r rs ih =>
    cases is with
    | nil => simp [check] at h
    | cons i is =>
      simp only [check,Bool.and_eq_true,decide_eq_true_eq] at h
      cases j with
      | zero => simpa only [Nat.add_zero,List.getElem?_cons_zero,Option.getD_some] using h.1
      | succ j =>
        have hh:=ih is (start+1) j (by simpa using hj) h.2
        simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,List.getElem?_cons_succ] using hh
end RHBatch01SequentialContourInput
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
open RHBatch01SequentialContourInput
noncomputable def v : List Nat := RHBatch01ContourSpectrumUpperZeroK02.rows.flatten
noncomputable def rr (c : Nat) : List Nat := (((RHBatch01ContourInputRUpperZeroK02.rows[30]?).getD []).drop (16*c)).take 16
noncomputable def ii (c : Nat) : List Nat := (((RHBatch01ContourInputIUpperZeroK02.rows[30]?).getD []).drop (16*c)).take 16
theorem checked00 : check v 15360
 ((RHBatch01ContourInputRUpperZeroK02.row30.drop 0).take 16) ((RHBatch01ContourInputIUpperZeroK02.row30.drop 0).take 16)=true ∧
 ((RHBatch01ContourInputRUpperZeroK02.row30.drop 0).take 16).length=16 := by decide +kernel
theorem checked01 : check v 15376
 ((RHBatch01ContourInputRUpperZeroK02.row30.drop 16).take 16) ((RHBatch01ContourInputIUpperZeroK02.row30.drop 16).take 16)=true ∧
 ((RHBatch01ContourInputRUpperZeroK02.row30.drop 16).take 16).length=16 := by decide +kernel
theorem checked02 : check v 15392
 ((RHBatch01ContourInputRUpperZeroK02.row30.drop 32).take 16) ((RHBatch01ContourInputIUpperZeroK02.row30.drop 32).take 16)=true ∧
 ((RHBatch01ContourInputRUpperZeroK02.row30.drop 32).take 16).length=16 := by decide +kernel
theorem checked03 : check v 15408
 ((RHBatch01ContourInputRUpperZeroK02.row30.drop 48).take 16) ((RHBatch01ContourInputIUpperZeroK02.row30.drop 48).take 16)=true ∧
 ((RHBatch01ContourInputRUpperZeroK02.row30.drop 48).take 16).length=16 := by decide +kernel
theorem checked04 : check v 15424
 ((RHBatch01ContourInputRUpperZeroK02.row30.drop 64).take 16) ((RHBatch01ContourInputIUpperZeroK02.row30.drop 64).take 16)=true ∧
 ((RHBatch01ContourInputRUpperZeroK02.row30.drop 64).take 16).length=16 := by decide +kernel
theorem checked05 : check v 15440
 ((RHBatch01ContourInputRUpperZeroK02.row30.drop 80).take 16) ((RHBatch01ContourInputIUpperZeroK02.row30.drop 80).take 16)=true ∧
 ((RHBatch01ContourInputRUpperZeroK02.row30.drop 80).take 16).length=16 := by decide +kernel
theorem checked06 : check v 15456
 ((RHBatch01ContourInputRUpperZeroK02.row30.drop 96).take 16) ((RHBatch01ContourInputIUpperZeroK02.row30.drop 96).take 16)=true ∧
 ((RHBatch01ContourInputRUpperZeroK02.row30.drop 96).take 16).length=16 := by decide +kernel
theorem checked07 : check v 15472
 ((RHBatch01ContourInputRUpperZeroK02.row30.drop 112).take 16) ((RHBatch01ContourInputIUpperZeroK02.row30.drop 112).take 16)=true ∧
 ((RHBatch01ContourInputRUpperZeroK02.row30.drop 112).take 16).length=16 := by decide +kernel
theorem checked08 : check v 15488
 ((RHBatch01ContourInputRUpperZeroK02.row30.drop 128).take 16) ((RHBatch01ContourInputIUpperZeroK02.row30.drop 128).take 16)=true ∧
 ((RHBatch01ContourInputRUpperZeroK02.row30.drop 128).take 16).length=16 := by decide +kernel
theorem checked09 : check v 15504
 ((RHBatch01ContourInputRUpperZeroK02.row30.drop 144).take 16) ((RHBatch01ContourInputIUpperZeroK02.row30.drop 144).take 16)=true ∧
 ((RHBatch01ContourInputRUpperZeroK02.row30.drop 144).take 16).length=16 := by decide +kernel
theorem checked10 : check v 15520
 ((RHBatch01ContourInputRUpperZeroK02.row30.drop 160).take 16) ((RHBatch01ContourInputIUpperZeroK02.row30.drop 160).take 16)=true ∧
 ((RHBatch01ContourInputRUpperZeroK02.row30.drop 160).take 16).length=16 := by decide +kernel
theorem checked11 : check v 15536
 ((RHBatch01ContourInputRUpperZeroK02.row30.drop 176).take 16) ((RHBatch01ContourInputIUpperZeroK02.row30.drop 176).take 16)=true ∧
 ((RHBatch01ContourInputRUpperZeroK02.row30.drop 176).take 16).length=16 := by decide +kernel
theorem checked12 : check v 15552
 ((RHBatch01ContourInputRUpperZeroK02.row30.drop 192).take 16) ((RHBatch01ContourInputIUpperZeroK02.row30.drop 192).take 16)=true ∧
 ((RHBatch01ContourInputRUpperZeroK02.row30.drop 192).take 16).length=16 := by decide +kernel
theorem checked13 : check v 15568
 ((RHBatch01ContourInputRUpperZeroK02.row30.drop 208).take 16) ((RHBatch01ContourInputIUpperZeroK02.row30.drop 208).take 16)=true ∧
 ((RHBatch01ContourInputRUpperZeroK02.row30.drop 208).take 16).length=16 := by decide +kernel
theorem checked14 : check v 15584
 ((RHBatch01ContourInputRUpperZeroK02.row30.drop 224).take 16) ((RHBatch01ContourInputIUpperZeroK02.row30.drop 224).take 16)=true ∧
 ((RHBatch01ContourInputRUpperZeroK02.row30.drop 224).take 16).length=16 := by decide +kernel
theorem checked15 : check v 15600
 ((RHBatch01ContourInputRUpperZeroK02.row30.drop 240).take 16) ((RHBatch01ContourInputIUpperZeroK02.row30.drop 240).take 16)=true ∧
 ((RHBatch01ContourInputRUpperZeroK02.row30.drop 240).take 16).length=16 := by decide +kernel
theorem checked16 : check v 15616
 ((RHBatch01ContourInputRUpperZeroK02.row30.drop 256).take 16) ((RHBatch01ContourInputIUpperZeroK02.row30.drop 256).take 16)=true ∧
 ((RHBatch01ContourInputRUpperZeroK02.row30.drop 256).take 16).length=16 := by decide +kernel
theorem checked17 : check v 15632
 ((RHBatch01ContourInputRUpperZeroK02.row30.drop 272).take 16) ((RHBatch01ContourInputIUpperZeroK02.row30.drop 272).take 16)=true ∧
 ((RHBatch01ContourInputRUpperZeroK02.row30.drop 272).take 16).length=16 := by decide +kernel
theorem checked18 : check v 15648
 ((RHBatch01ContourInputRUpperZeroK02.row30.drop 288).take 16) ((RHBatch01ContourInputIUpperZeroK02.row30.drop 288).take 16)=true ∧
 ((RHBatch01ContourInputRUpperZeroK02.row30.drop 288).take 16).length=16 := by decide +kernel
theorem checked19 : check v 15664
 ((RHBatch01ContourInputRUpperZeroK02.row30.drop 304).take 16) ((RHBatch01ContourInputIUpperZeroK02.row30.drop 304).take 16)=true ∧
 ((RHBatch01ContourInputRUpperZeroK02.row30.drop 304).take 16).length=16 := by decide +kernel
theorem checked20 : check v 15680
 ((RHBatch01ContourInputRUpperZeroK02.row30.drop 320).take 16) ((RHBatch01ContourInputIUpperZeroK02.row30.drop 320).take 16)=true ∧
 ((RHBatch01ContourInputRUpperZeroK02.row30.drop 320).take 16).length=16 := by decide +kernel
theorem checked21 : check v 15696
 ((RHBatch01ContourInputRUpperZeroK02.row30.drop 336).take 16) ((RHBatch01ContourInputIUpperZeroK02.row30.drop 336).take 16)=true ∧
 ((RHBatch01ContourInputRUpperZeroK02.row30.drop 336).take 16).length=16 := by decide +kernel
theorem checked22 : check v 15712
 ((RHBatch01ContourInputRUpperZeroK02.row30.drop 352).take 16) ((RHBatch01ContourInputIUpperZeroK02.row30.drop 352).take 16)=true ∧
 ((RHBatch01ContourInputRUpperZeroK02.row30.drop 352).take 16).length=16 := by decide +kernel
theorem checked23 : check v 15728
 ((RHBatch01ContourInputRUpperZeroK02.row30.drop 368).take 16) ((RHBatch01ContourInputIUpperZeroK02.row30.drop 368).take 16)=true ∧
 ((RHBatch01ContourInputRUpperZeroK02.row30.drop 368).take 16).length=16 := by decide +kernel
theorem checked24 : check v 15744
 ((RHBatch01ContourInputRUpperZeroK02.row30.drop 384).take 16) ((RHBatch01ContourInputIUpperZeroK02.row30.drop 384).take 16)=true ∧
 ((RHBatch01ContourInputRUpperZeroK02.row30.drop 384).take 16).length=16 := by decide +kernel
theorem checked25 : check v 15760
 ((RHBatch01ContourInputRUpperZeroK02.row30.drop 400).take 16) ((RHBatch01ContourInputIUpperZeroK02.row30.drop 400).take 16)=true ∧
 ((RHBatch01ContourInputRUpperZeroK02.row30.drop 400).take 16).length=16 := by decide +kernel
theorem checked26 : check v 15776
 ((RHBatch01ContourInputRUpperZeroK02.row30.drop 416).take 16) ((RHBatch01ContourInputIUpperZeroK02.row30.drop 416).take 16)=true ∧
 ((RHBatch01ContourInputRUpperZeroK02.row30.drop 416).take 16).length=16 := by decide +kernel
theorem checked27 : check v 15792
 ((RHBatch01ContourInputRUpperZeroK02.row30.drop 432).take 16) ((RHBatch01ContourInputIUpperZeroK02.row30.drop 432).take 16)=true ∧
 ((RHBatch01ContourInputRUpperZeroK02.row30.drop 432).take 16).length=16 := by decide +kernel
theorem checked28 : check v 15808
 ((RHBatch01ContourInputRUpperZeroK02.row30.drop 448).take 16) ((RHBatch01ContourInputIUpperZeroK02.row30.drop 448).take 16)=true ∧
 ((RHBatch01ContourInputRUpperZeroK02.row30.drop 448).take 16).length=16 := by decide +kernel
theorem checked29 : check v 15824
 ((RHBatch01ContourInputRUpperZeroK02.row30.drop 464).take 16) ((RHBatch01ContourInputIUpperZeroK02.row30.drop 464).take 16)=true ∧
 ((RHBatch01ContourInputRUpperZeroK02.row30.drop 464).take 16).length=16 := by decide +kernel
theorem checked30 : check v 15840
 ((RHBatch01ContourInputRUpperZeroK02.row30.drop 480).take 16) ((RHBatch01ContourInputIUpperZeroK02.row30.drop 480).take 16)=true ∧
 ((RHBatch01ContourInputRUpperZeroK02.row30.drop 480).take 16).length=16 := by decide +kernel
theorem checked31 : check v 15856
 ((RHBatch01ContourInputRUpperZeroK02.row30.drop 496).take 16) ((RHBatch01ContourInputIUpperZeroK02.row30.drop 496).take 16)=true ∧
 ((RHBatch01ContourInputRUpperZeroK02.row30.drop 496).take 16).length=16 := by decide +kernel
lemma all_checked (c : Nat) (hc:c<32) :
 check v (15360+16*c) (rr c) (ii c)=true ∧ (rr c).length=16 := by
 interval_cases c
 · exact checked00
 · exact checked01
 · exact checked02
 · exact checked03
 · exact checked04
 · exact checked05
 · exact checked06
 · exact checked07
 · exact checked08
 · exact checked09
 · exact checked10
 · exact checked11
 · exact checked12
 · exact checked13
 · exact checked14
 · exact checked15
 · exact checked16
 · exact checked17
 · exact checked18
 · exact checked19
 · exact checked20
 · exact checked21
 · exact checked22
 · exact checked23
 · exact checked24
 · exact checked25
 · exact checked26
 · exact checked27
 · exact checked28
 · exact checked29
 · exact checked30
 · exact checked31
end RHBatch01SparseSliceRHBatch01ContourActualInputUpperZeroK02B30
theorem TaoFivePrimes.rh_batch01_height_contour_actual_input_upper_zero_k02_slice30 :
 ∀i:Nat,i<512 →
 RHHighContourVector.raw RHBatch01ContourSpectrumUpperZeroK02.rows.flatten RHHighFFTArithmeticBase.chirp (15360+i)=
  ((((((RHBatch01ContourInputRUpperZeroK02.rows[30]?).getD [])[i]?).getD 0:Nat):Int)-2^166,
   (((((RHBatch01ContourInputIUpperZeroK02.rows[30]?).getD [])[i]?).getD 0:Nat):Int)-2^166) ∧
  ((((RHBatch01ContourInputRUpperZeroK02.rows[30]?).getD [])[i]?).getD 0)≤2^167 ∧
  ((((RHBatch01ContourInputIUpperZeroK02.rows[30]?).getD [])[i]?).getD 0)≤2^167 := by
 intro i hi
 have h:=RHBatch01SparseSliceRHBatch01ContourActualInputUpperZeroK02B30.all_checked (i/16) (by omega)
 have hh:=RHBatch01SparseSliceRHBatch01ContourActualInputUpperZeroK02B30.RHBatch01SequentialContourInput.sound RHBatch01SparseSliceRHBatch01ContourActualInputUpperZeroK02B30.v (RHBatch01SparseSliceRHBatch01ContourActualInputUpperZeroK02B30.rr (i/16)) (RHBatch01SparseSliceRHBatch01ContourActualInputUpperZeroK02B30.ii (i/16))
  (15360+16*(i/16)) (i%16) (by rw[h.2];omega) h.1
 have he:16*(i/16)+i%16=i:=by omega
 simpa only[RHBatch01SparseSliceRHBatch01ContourActualInputUpperZeroK02B30.v,RHBatch01SparseSliceRHBatch01ContourActualInputUpperZeroK02B30.rr,RHBatch01SparseSliceRHBatch01ContourActualInputUpperZeroK02B30.ii,List.getElem?_take,List.getElem?_drop,
  show i%16<16 by omega,if_true,show 15360+16*(i/16)+i%16=15360+i by omega,he] using hh
namespace RHBatch01SparseSliceRHBatch01ContourActualInputUpperZeroK02B31
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace RHBatch01SequentialContourInput
noncomputable def check (v : List Nat) (start : Nat) : List Nat→List Nat→Bool
  | [],[] => true
  | r::rs,i::is => decide (RHHighContourVector.raw v RHHighFFTArithmeticBase.chirp start=
      ((r:Int)-2^166,(i:Int)-2^166) ∧ r≤2^167 ∧ i≤2^167) && check v (start+1) rs is
  | _,_ => false
lemma sound (v rs is : List Nat) (start j : Nat) (hj:j< rs.length)
    (h:check v start rs is=true) :
    RHHighContourVector.raw v RHHighFFTArithmeticBase.chirp (start+j)=
      ((((rs[j]?).getD 0:Nat):Int)-2^166,(((is[j]?).getD 0:Nat):Int)-2^166) ∧
      ((rs[j]?).getD 0)≤2^167 ∧ ((is[j]?).getD 0)≤2^167 := by
  induction rs generalizing start j is with
  | nil => simp at hj
  | cons r rs ih =>
    cases is with
    | nil => simp [check] at h
    | cons i is =>
      simp only [check,Bool.and_eq_true,decide_eq_true_eq] at h
      cases j with
      | zero => simpa only [Nat.add_zero,List.getElem?_cons_zero,Option.getD_some] using h.1
      | succ j =>
        have hh:=ih is (start+1) j (by simpa using hj) h.2
        simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,List.getElem?_cons_succ] using hh
end RHBatch01SequentialContourInput
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
open RHBatch01SequentialContourInput
noncomputable def v : List Nat := RHBatch01ContourSpectrumUpperZeroK02.rows.flatten
noncomputable def rr (c : Nat) : List Nat := (((RHBatch01ContourInputRUpperZeroK02.rows[31]?).getD []).drop (16*c)).take 16
noncomputable def ii (c : Nat) : List Nat := (((RHBatch01ContourInputIUpperZeroK02.rows[31]?).getD []).drop (16*c)).take 16
theorem checked00 : check v 15872
 ((RHBatch01ContourInputRUpperZeroK02.row31.drop 0).take 16) ((RHBatch01ContourInputIUpperZeroK02.row31.drop 0).take 16)=true ∧
 ((RHBatch01ContourInputRUpperZeroK02.row31.drop 0).take 16).length=16 := by decide +kernel
theorem checked01 : check v 15888
 ((RHBatch01ContourInputRUpperZeroK02.row31.drop 16).take 16) ((RHBatch01ContourInputIUpperZeroK02.row31.drop 16).take 16)=true ∧
 ((RHBatch01ContourInputRUpperZeroK02.row31.drop 16).take 16).length=16 := by decide +kernel
theorem checked02 : check v 15904
 ((RHBatch01ContourInputRUpperZeroK02.row31.drop 32).take 16) ((RHBatch01ContourInputIUpperZeroK02.row31.drop 32).take 16)=true ∧
 ((RHBatch01ContourInputRUpperZeroK02.row31.drop 32).take 16).length=16 := by decide +kernel
theorem checked03 : check v 15920
 ((RHBatch01ContourInputRUpperZeroK02.row31.drop 48).take 16) ((RHBatch01ContourInputIUpperZeroK02.row31.drop 48).take 16)=true ∧
 ((RHBatch01ContourInputRUpperZeroK02.row31.drop 48).take 16).length=16 := by decide +kernel
theorem checked04 : check v 15936
 ((RHBatch01ContourInputRUpperZeroK02.row31.drop 64).take 16) ((RHBatch01ContourInputIUpperZeroK02.row31.drop 64).take 16)=true ∧
 ((RHBatch01ContourInputRUpperZeroK02.row31.drop 64).take 16).length=16 := by decide +kernel
theorem checked05 : check v 15952
 ((RHBatch01ContourInputRUpperZeroK02.row31.drop 80).take 16) ((RHBatch01ContourInputIUpperZeroK02.row31.drop 80).take 16)=true ∧
 ((RHBatch01ContourInputRUpperZeroK02.row31.drop 80).take 16).length=16 := by decide +kernel
theorem checked06 : check v 15968
 ((RHBatch01ContourInputRUpperZeroK02.row31.drop 96).take 16) ((RHBatch01ContourInputIUpperZeroK02.row31.drop 96).take 16)=true ∧
 ((RHBatch01ContourInputRUpperZeroK02.row31.drop 96).take 16).length=16 := by decide +kernel
theorem checked07 : check v 15984
 ((RHBatch01ContourInputRUpperZeroK02.row31.drop 112).take 16) ((RHBatch01ContourInputIUpperZeroK02.row31.drop 112).take 16)=true ∧
 ((RHBatch01ContourInputRUpperZeroK02.row31.drop 112).take 16).length=16 := by decide +kernel
theorem checked08 : check v 16000
 ((RHBatch01ContourInputRUpperZeroK02.row31.drop 128).take 16) ((RHBatch01ContourInputIUpperZeroK02.row31.drop 128).take 16)=true ∧
 ((RHBatch01ContourInputRUpperZeroK02.row31.drop 128).take 16).length=16 := by decide +kernel
theorem checked09 : check v 16016
 ((RHBatch01ContourInputRUpperZeroK02.row31.drop 144).take 16) ((RHBatch01ContourInputIUpperZeroK02.row31.drop 144).take 16)=true ∧
 ((RHBatch01ContourInputRUpperZeroK02.row31.drop 144).take 16).length=16 := by decide +kernel
theorem checked10 : check v 16032
 ((RHBatch01ContourInputRUpperZeroK02.row31.drop 160).take 16) ((RHBatch01ContourInputIUpperZeroK02.row31.drop 160).take 16)=true ∧
 ((RHBatch01ContourInputRUpperZeroK02.row31.drop 160).take 16).length=16 := by decide +kernel
theorem checked11 : check v 16048
 ((RHBatch01ContourInputRUpperZeroK02.row31.drop 176).take 16) ((RHBatch01ContourInputIUpperZeroK02.row31.drop 176).take 16)=true ∧
 ((RHBatch01ContourInputRUpperZeroK02.row31.drop 176).take 16).length=16 := by decide +kernel
theorem checked12 : check v 16064
 ((RHBatch01ContourInputRUpperZeroK02.row31.drop 192).take 16) ((RHBatch01ContourInputIUpperZeroK02.row31.drop 192).take 16)=true ∧
 ((RHBatch01ContourInputRUpperZeroK02.row31.drop 192).take 16).length=16 := by decide +kernel
theorem checked13 : check v 16080
 ((RHBatch01ContourInputRUpperZeroK02.row31.drop 208).take 16) ((RHBatch01ContourInputIUpperZeroK02.row31.drop 208).take 16)=true ∧
 ((RHBatch01ContourInputRUpperZeroK02.row31.drop 208).take 16).length=16 := by decide +kernel
theorem checked14 : check v 16096
 ((RHBatch01ContourInputRUpperZeroK02.row31.drop 224).take 16) ((RHBatch01ContourInputIUpperZeroK02.row31.drop 224).take 16)=true ∧
 ((RHBatch01ContourInputRUpperZeroK02.row31.drop 224).take 16).length=16 := by decide +kernel
theorem checked15 : check v 16112
 ((RHBatch01ContourInputRUpperZeroK02.row31.drop 240).take 16) ((RHBatch01ContourInputIUpperZeroK02.row31.drop 240).take 16)=true ∧
 ((RHBatch01ContourInputRUpperZeroK02.row31.drop 240).take 16).length=16 := by decide +kernel
theorem checked16 : check v 16128
 ((RHBatch01ContourInputRUpperZeroK02.row31.drop 256).take 16) ((RHBatch01ContourInputIUpperZeroK02.row31.drop 256).take 16)=true ∧
 ((RHBatch01ContourInputRUpperZeroK02.row31.drop 256).take 16).length=16 := by decide +kernel
theorem checked17 : check v 16144
 ((RHBatch01ContourInputRUpperZeroK02.row31.drop 272).take 16) ((RHBatch01ContourInputIUpperZeroK02.row31.drop 272).take 16)=true ∧
 ((RHBatch01ContourInputRUpperZeroK02.row31.drop 272).take 16).length=16 := by decide +kernel
theorem checked18 : check v 16160
 ((RHBatch01ContourInputRUpperZeroK02.row31.drop 288).take 16) ((RHBatch01ContourInputIUpperZeroK02.row31.drop 288).take 16)=true ∧
 ((RHBatch01ContourInputRUpperZeroK02.row31.drop 288).take 16).length=16 := by decide +kernel
theorem checked19 : check v 16176
 ((RHBatch01ContourInputRUpperZeroK02.row31.drop 304).take 16) ((RHBatch01ContourInputIUpperZeroK02.row31.drop 304).take 16)=true ∧
 ((RHBatch01ContourInputRUpperZeroK02.row31.drop 304).take 16).length=16 := by decide +kernel
theorem checked20 : check v 16192
 ((RHBatch01ContourInputRUpperZeroK02.row31.drop 320).take 16) ((RHBatch01ContourInputIUpperZeroK02.row31.drop 320).take 16)=true ∧
 ((RHBatch01ContourInputRUpperZeroK02.row31.drop 320).take 16).length=16 := by decide +kernel
theorem checked21 : check v 16208
 ((RHBatch01ContourInputRUpperZeroK02.row31.drop 336).take 16) ((RHBatch01ContourInputIUpperZeroK02.row31.drop 336).take 16)=true ∧
 ((RHBatch01ContourInputRUpperZeroK02.row31.drop 336).take 16).length=16 := by decide +kernel
theorem checked22 : check v 16224
 ((RHBatch01ContourInputRUpperZeroK02.row31.drop 352).take 16) ((RHBatch01ContourInputIUpperZeroK02.row31.drop 352).take 16)=true ∧
 ((RHBatch01ContourInputRUpperZeroK02.row31.drop 352).take 16).length=16 := by decide +kernel
theorem checked23 : check v 16240
 ((RHBatch01ContourInputRUpperZeroK02.row31.drop 368).take 16) ((RHBatch01ContourInputIUpperZeroK02.row31.drop 368).take 16)=true ∧
 ((RHBatch01ContourInputRUpperZeroK02.row31.drop 368).take 16).length=16 := by decide +kernel
theorem checked24 : check v 16256
 ((RHBatch01ContourInputRUpperZeroK02.row31.drop 384).take 16) ((RHBatch01ContourInputIUpperZeroK02.row31.drop 384).take 16)=true ∧
 ((RHBatch01ContourInputRUpperZeroK02.row31.drop 384).take 16).length=16 := by decide +kernel
theorem checked25 : check v 16272
 ((RHBatch01ContourInputRUpperZeroK02.row31.drop 400).take 16) ((RHBatch01ContourInputIUpperZeroK02.row31.drop 400).take 16)=true ∧
 ((RHBatch01ContourInputRUpperZeroK02.row31.drop 400).take 16).length=16 := by decide +kernel
theorem checked26 : check v 16288
 ((RHBatch01ContourInputRUpperZeroK02.row31.drop 416).take 16) ((RHBatch01ContourInputIUpperZeroK02.row31.drop 416).take 16)=true ∧
 ((RHBatch01ContourInputRUpperZeroK02.row31.drop 416).take 16).length=16 := by decide +kernel
theorem checked27 : check v 16304
 ((RHBatch01ContourInputRUpperZeroK02.row31.drop 432).take 16) ((RHBatch01ContourInputIUpperZeroK02.row31.drop 432).take 16)=true ∧
 ((RHBatch01ContourInputRUpperZeroK02.row31.drop 432).take 16).length=16 := by decide +kernel
theorem checked28 : check v 16320
 ((RHBatch01ContourInputRUpperZeroK02.row31.drop 448).take 16) ((RHBatch01ContourInputIUpperZeroK02.row31.drop 448).take 16)=true ∧
 ((RHBatch01ContourInputRUpperZeroK02.row31.drop 448).take 16).length=16 := by decide +kernel
theorem checked29 : check v 16336
 ((RHBatch01ContourInputRUpperZeroK02.row31.drop 464).take 16) ((RHBatch01ContourInputIUpperZeroK02.row31.drop 464).take 16)=true ∧
 ((RHBatch01ContourInputRUpperZeroK02.row31.drop 464).take 16).length=16 := by decide +kernel
theorem checked30 : check v 16352
 ((RHBatch01ContourInputRUpperZeroK02.row31.drop 480).take 16) ((RHBatch01ContourInputIUpperZeroK02.row31.drop 480).take 16)=true ∧
 ((RHBatch01ContourInputRUpperZeroK02.row31.drop 480).take 16).length=16 := by decide +kernel
theorem checked31 : check v 16368
 ((RHBatch01ContourInputRUpperZeroK02.row31.drop 496).take 16) ((RHBatch01ContourInputIUpperZeroK02.row31.drop 496).take 16)=true ∧
 ((RHBatch01ContourInputRUpperZeroK02.row31.drop 496).take 16).length=16 := by decide +kernel
lemma all_checked (c : Nat) (hc:c<32) :
 check v (15872+16*c) (rr c) (ii c)=true ∧ (rr c).length=16 := by
 interval_cases c
 · exact checked00
 · exact checked01
 · exact checked02
 · exact checked03
 · exact checked04
 · exact checked05
 · exact checked06
 · exact checked07
 · exact checked08
 · exact checked09
 · exact checked10
 · exact checked11
 · exact checked12
 · exact checked13
 · exact checked14
 · exact checked15
 · exact checked16
 · exact checked17
 · exact checked18
 · exact checked19
 · exact checked20
 · exact checked21
 · exact checked22
 · exact checked23
 · exact checked24
 · exact checked25
 · exact checked26
 · exact checked27
 · exact checked28
 · exact checked29
 · exact checked30
 · exact checked31
end RHBatch01SparseSliceRHBatch01ContourActualInputUpperZeroK02B31
theorem TaoFivePrimes.rh_batch01_height_contour_actual_input_upper_zero_k02_slice31 :
 ∀i:Nat,i<512 →
 RHHighContourVector.raw RHBatch01ContourSpectrumUpperZeroK02.rows.flatten RHHighFFTArithmeticBase.chirp (15872+i)=
  ((((((RHBatch01ContourInputRUpperZeroK02.rows[31]?).getD [])[i]?).getD 0:Nat):Int)-2^166,
   (((((RHBatch01ContourInputIUpperZeroK02.rows[31]?).getD [])[i]?).getD 0:Nat):Int)-2^166) ∧
  ((((RHBatch01ContourInputRUpperZeroK02.rows[31]?).getD [])[i]?).getD 0)≤2^167 ∧
  ((((RHBatch01ContourInputIUpperZeroK02.rows[31]?).getD [])[i]?).getD 0)≤2^167 := by
 intro i hi
 have h:=RHBatch01SparseSliceRHBatch01ContourActualInputUpperZeroK02B31.all_checked (i/16) (by omega)
 have hh:=RHBatch01SparseSliceRHBatch01ContourActualInputUpperZeroK02B31.RHBatch01SequentialContourInput.sound RHBatch01SparseSliceRHBatch01ContourActualInputUpperZeroK02B31.v (RHBatch01SparseSliceRHBatch01ContourActualInputUpperZeroK02B31.rr (i/16)) (RHBatch01SparseSliceRHBatch01ContourActualInputUpperZeroK02B31.ii (i/16))
  (15872+16*(i/16)) (i%16) (by rw[h.2];omega) h.1
 have he:16*(i/16)+i%16=i:=by omega
 simpa only[RHBatch01SparseSliceRHBatch01ContourActualInputUpperZeroK02B31.v,RHBatch01SparseSliceRHBatch01ContourActualInputUpperZeroK02B31.rr,RHBatch01SparseSliceRHBatch01ContourActualInputUpperZeroK02B31.ii,List.getElem?_take,List.getElem?_drop,
  show i%16<16 by omega,if_true,show 15872+16*(i/16)+i%16=15872+i by omega,he] using hh
namespace RHBatch01SparseAggregateRHBatch01ContourActualInputUpperZeroK02
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace RHBatch01FlatRows
lemma lookup {α : Type} (d : Nat) (hd:0< d) (a : α) (rows : List (List α))
    (hle:∀ r∈rows,r.length≤ d) (hfull:∀ r∈rows.dropLast,r.length=d)
    (i : Nat) (hi:i< rows.flatten.length) :
    ((rows.flatten[i]?).getD a)=((((rows[i/d]?).getD [])[i%d]?).getD a) := by
  induction rows generalizing i with
  | nil => simp at hi
  | cons xs xss ih =>
    cases xss with
    | nil =>
      have hx:xs.length≤ d:=hle xs (by simp)
      have hi':i< xs.length:=by simpa only [List.flatten_cons,List.flatten_nil,List.append_nil] using hi
      have hid:i< d:=by omega
      simp only [List.flatten_cons,List.flatten_nil,List.append_nil,Nat.div_eq_of_lt hid,
        Nat.mod_eq_of_lt hid,List.getElem?_cons_zero,Option.getD_some]
    | cons ys yss =>
      have hx:xs.length=d:=hfull xs (by simp only [List.dropLast_cons_cons,List.mem_cons,true_or])
      have hle':∀ r∈ys::yss,r.length≤ d:=by intro r hr;exact hle r (List.mem_cons_of_mem _ hr)
      have hfull':∀ r∈(ys::yss).dropLast,r.length=d:=by
        intro r hr
        apply hfull r
        simp only [List.dropLast_cons_cons,List.mem_cons]
        exact Or.inr hr
      by_cases hid:i< d
      · rw [List.flatten_cons,List.getElem?_append_left (by omega),Nat.div_eq_of_lt hid,
          Nat.mod_eq_of_lt hid,List.getElem?_cons_zero,Option.getD_some]
      · have hdle:d≤ i:=by omega
        have he:i-d+d=i:=Nat.sub_add_cancel hdle
        have hdv:i/d=(i-d)/d+1 := by
          calc i/d=(i-d+d)/d:=by rw [he]
               _=(i-d)/d+1:=Nat.add_div_right _ hd
        have hmod:i%d=(i-d)%d := by
          calc i%d=(i-d+d)%d:=by rw [he]
               _=(i-d)%d:=Nat.add_mod_right _ _
        have hit:i-d<(ys::yss).flatten.length := by
          have hlen:(xs::ys::yss).flatten.length=d+(ys::yss).flatten.length:=by
            simp only [List.flatten_cons,List.length_append,hx]
          rw [hlen] at hi
          omega
        rw [List.flatten_cons,List.getElem?_append_right (by omega),hx,hdv,hmod,List.getElem?_cons_succ]
        exact ih hle' hfull' (i-d) hit
end RHBatch01FlatRows
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace RHBatch01FFTListInterface
noncomputable def entry (xs : List Nat) (j : Nat) : Nat := (xs[j]?).getD 0
lemma ofFn_at {N : Nat} (xs : List Nat) (h:xs.length=N) :
    List.ofFn (fun j:Fin N=> entry xs j.val)=xs := by
  apply List.ext_getElem
  · simpa only [List.length_ofFn] using h.symm
  · intro j hj hj'
    simp only [List.getElem_ofFn,entry,List.getElem?_eq_getElem hj',Option.getD_some]
lemma bounded_at (xs : List Nat) (M : Nat)
    (h:xs.all (fun x=> decide (x≤ M))=true) (j : Nat) : entry xs j≤ M := by
  by_cases hj:j< xs.length
  · rw [entry,List.getElem?_eq_getElem hj,Option.getD_some]
    exact decide_eq_true_eq.mp ((List.all_eq_true.mp h) _ (List.getElem_mem hj))
  · have he:xs[j]?=none:=List.getElem?_eq_none (by omega)
    simp only [entry,he,Option.getD_none]
    exact Nat.zero_le _
lemma flatten_bounded (rows : List (List Nat)) (M : Nat)
    (h:rows.all (fun row=> decide (row.length=512) && row.all (fun x=> decide (x≤ M)))=true) :
    rows.flatten.all (fun x=> decide (x≤ M))=true := by
  apply List.all_eq_true.mpr
  intro x hx
  obtain ⟨row,hr,hx⟩:=List.mem_flatten.mp hx
  have hh:=(List.all_eq_true.mp h) row hr
  simp only [Bool.and_eq_true,decide_eq_true_eq] at hh
  exact (List.all_eq_true.mp hh.2) x hx
lemma uniform_lookup (rows : List (List Nat)) (i : Nat)
    (h:rows.all (fun row=> decide (row.length=512))=true)
    (hi:i< rows.flatten.length) :
    entry rows.flatten i=(((rows[i/512]?).getD [])[i%512]?).getD 0 := by
  unfold entry
  apply RHBatch01FlatRows.lookup 512 (by decide) 0 rows
  · intro row hr
    exact (decide_eq_true_eq.mp ((List.all_eq_true.mp h) row hr)).le
  · intro row hr
    apply decide_eq_true_eq.mp
    exact (List.all_eq_true.mp h) row (List.mem_of_mem_dropLast hr)
  · exact hi
lemma lengths_from_bound (rows : List (List Nat)) (M : Nat)
    (h:rows.all (fun row=> decide (row.length=512) && row.all (fun x=> decide (x≤ M)))=true) :
    rows.all (fun row=> decide (row.length=512))=true := by
  apply List.all_eq_true.mpr
  intro row hr
  have hh:=(List.all_eq_true.mp h) row hr
  simp only [Bool.and_eq_true] at hh
  exact hh.1
end RHBatch01FFTListInterface
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
namespace RHBatch01SparseInput
open RHBatch01FFTListInterface
lemma middle_at (xs : List Nat) (i : Nat) (hlen:xs.length=16384) (hi:1025 ≤ i ∧ i<15360)
 (h:((xs.drop 1025).take 14335).all (fun x=> decide (x=2^166))=true) : entry xs i=2^166 := by
 let j:=i-1025
 have hj:j<14335:=by dsimp[j];omega
 have hl:((xs.drop 1025).take 14335).length=14335:=by simp only[List.length_take,List.length_drop,hlen];decide
 have hh:=(List.all_eq_true.mp h) (((xs.drop 1025).take 14335)[j]) (List.getElem_mem (by rw[hl];exact hj))
 have heq:(((xs.drop 1025).take 14335)[j]?).getD 0=(((xs.drop 1025).take 14335)[j]):=by rw[List.getElem?_eq_getElem (by rw[hl];exact hj),Option.getD_some]
 rw[←heq] at hh
 have he:1025+j=i:=by dsimp[j];omega
 simpa only[List.getElem?_take,List.getElem?_drop,hj,if_true,he,decide_eq_true_eq,entry] using hh
lemma raw_zero (v : List Nat) (chirp : Nat→Int×Int) (i : Nat) (hi:1025 ≤ i ∧ i<15360) :
 RHHighContourVector.raw v chirp i=(0,0) := by
 have hv:RHHighContourVector.vector v i=(0,0):=by
  simp only[RHHighContourVector.vector,if_neg (show i≠0 by omega),
   if_neg (show ¬i≤1024 by omega),if_neg (show ¬15360≤ i by omega)]
 simp only[RHHighContourVector.raw,hv,Prod.fst,Prod.snd,zero_mul,zero_add,zero_sub,neg_zero]
end RHBatch01SparseInput
end
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
open RHBatch01FFTListInterface RHBatch01SparseInput
theorem real_shapes : RHBatch01ContourInputRUpperZeroK02.rows.flatten.length=16384 ∧ RHBatch01ContourInputRUpperZeroK02.rows.all (fun row=> decide (row.length=512))=true := by decide +kernel
theorem imag_shapes : RHBatch01ContourInputIUpperZeroK02.rows.flatten.length=16384 ∧ RHBatch01ContourInputIUpperZeroK02.rows.all (fun row=> decide (row.length=512))=true := by decide +kernel
theorem real_middle : ((RHBatch01ContourInputRUpperZeroK02.rows.flatten.drop 1025).take 14335).all (fun x=> decide (x=2^166))=true := by decide +kernel
theorem imag_middle : ((RHBatch01ContourInputIUpperZeroK02.rows.flatten.drop 1025).take 14335).all (fun x=> decide (x=2^166))=true := by decide +kernel
end RHBatch01SparseAggregateRHBatch01ContourActualInputUpperZeroK02
open RHBatch01SparseAggregateRHBatch01ContourActualInputUpperZeroK02
theorem solution :
 ∀ i : Nat,i<16384 →
 RHHighContourVector.raw RHBatch01ContourSpectrumUpperZeroK02.rows.flatten RHHighFFTArithmeticBase.chirp i=
  (((((RHBatch01ContourInputRUpperZeroK02.rows[i/512]?).getD [])[i%512]?).getD 0:Int)-2^166,
   ((((RHBatch01ContourInputIUpperZeroK02.rows[i/512]?).getD [])[i%512]?).getD 0:Int)-2^166) ∧
  ((((RHBatch01ContourInputRUpperZeroK02.rows[i/512]?).getD [])[i%512]?).getD 0)≤2^167 ∧
  ((((RHBatch01ContourInputIUpperZeroK02.rows[i/512]?).getD [])[i%512]?).getD 0)≤2^167 := by
 intro i hi
 by_cases hmid:1025 ≤ i ∧ i<15360
 · have hR:=RHBatch01SparseInput.middle_at RHBatch01ContourInputRUpperZeroK02.rows.flatten i real_shapes.1 hmid real_middle
   have hI:=RHBatch01SparseInput.middle_at RHBatch01ContourInputIUpperZeroK02.rows.flatten i imag_shapes.1 hmid imag_middle
   rw[RHBatch01FFTListInterface.uniform_lookup RHBatch01ContourInputRUpperZeroK02.rows i real_shapes.2 (by rw[real_shapes.1];exact hi)] at hR
   rw[RHBatch01FFTListInterface.uniform_lookup RHBatch01ContourInputIUpperZeroK02.rows i imag_shapes.2 (by rw[imag_shapes.1];exact hi)] at hI
   rw[RHBatch01SparseInput.raw_zero _ _ i hmid,hR,hI]
   norm_num
 · have hb:i/512=0 ∨ i/512=1 ∨ i/512=2 ∨ i/512=30 ∨ i/512=31 := by omega
   have he:512*(i/512)+i%512=i:=by omega
   rcases hb with hb|hb|hb|hb|hb
   · have h:=TaoFivePrimes.rh_batch01_height_contour_actual_input_upper_zero_k02_slice00 (i%512) (by omega : i%512<512)
     have he':0+i%512=i:=by omega
     simpa only [hb,he'] using h
   · have h:=TaoFivePrimes.rh_batch01_height_contour_actual_input_upper_zero_k02_slice01 (i%512) (by omega : i%512<512)
     have he':512+i%512=i:=by omega
     simpa only [hb,he'] using h
   · have h:=TaoFivePrimes.rh_batch01_height_contour_actual_input_upper_zero_k02_slice02 (i%512) (by omega : i%512<1)
     have he':1024+i%512=i:=by omega
     simpa only [hb,he'] using h
   · have h:=TaoFivePrimes.rh_batch01_height_contour_actual_input_upper_zero_k02_slice30 (i%512) (by omega : i%512<512)
     have he':15360+i%512=i:=by omega
     simpa only [hb,he'] using h
   · have h:=TaoFivePrimes.rh_batch01_height_contour_actual_input_upper_zero_k02_slice31 (i%512) (by omega : i%512<512)
     have he':15872+i%512=i:=by omega
     simpa only [hb,he'] using h
#print axioms solution
