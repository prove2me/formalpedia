-- Prove2me | solution 1 for TaoFivePrimes.rh_batch01_height_contour_actual_input_upper_neg64_k00
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T20:13:19.712796+00:00
-- url     : https://prove2.me/submissions/7d05047d-fe56-4862-a72f-1f49323a6a2f

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighContourVector
import Definitions.Def_TaoFivePrimes_RHHighFFTArithmeticBase
import Definitions.Def_TaoFivePrimes_RHBatch01ContourInputR00
import Definitions.Def_TaoFivePrimes_RHBatch01ContourInputI00
import Definitions.Def_TaoFivePrimes_RHBatch01ContourSpectrumUpperNeg64K00
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace RHBatch01SequentialContourInput
noncomputable def check (v : List Nat) (start : Nat) : List Nat→List Nat→Bool
  | [],[] => true
  | r::rs,i::is => decide (RHHighContourVector.raw v RHHighFFTArithmeticBase.chirp start=
      ((r:Int)-2^166,(i:Int)-2^166) ∧ r≤2^167 ∧ i≤2^167) && check v (start+1) rs is
  | _,_ => false
lemma sound (v rs is : List Nat) (start j : Nat) (hj:j<rs.length)
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
namespace RHBatch01ActualContourInputUpperNeg64K00
open RHBatch01SequentialContourInput
noncomputable def v : List Nat := RHBatch01ContourSpectrumUpperNeg64K00.rows.flatten
noncomputable def realRow (b c : Nat) : List Nat := (((RHBatch01ContourInputR00.rows[b]?).getD []).drop (16*c)).take 16
noncomputable def imagRow (b c : Nat) : List Nat := (((RHBatch01ContourInputI00.rows[b]?).getD []).drop (16*c)).take 16
theorem checked00_00 : check v 0
 ((RHBatch01ContourInputR00.row00.drop 0).take 16) ((RHBatch01ContourInputI00.row00.drop 0).take 16)=true ∧
 ((RHBatch01ContourInputR00.row00.drop 0).take 16).length=16 := by decide +kernel
theorem checked00_01 : check v 16
 ((RHBatch01ContourInputR00.row00.drop 16).take 16) ((RHBatch01ContourInputI00.row00.drop 16).take 16)=true ∧
 ((RHBatch01ContourInputR00.row00.drop 16).take 16).length=16 := by decide +kernel
theorem checked00_02 : check v 32
 ((RHBatch01ContourInputR00.row00.drop 32).take 16) ((RHBatch01ContourInputI00.row00.drop 32).take 16)=true ∧
 ((RHBatch01ContourInputR00.row00.drop 32).take 16).length=16 := by decide +kernel
theorem checked00_03 : check v 48
 ((RHBatch01ContourInputR00.row00.drop 48).take 16) ((RHBatch01ContourInputI00.row00.drop 48).take 16)=true ∧
 ((RHBatch01ContourInputR00.row00.drop 48).take 16).length=16 := by decide +kernel
theorem checked00_04 : check v 64
 ((RHBatch01ContourInputR00.row00.drop 64).take 16) ((RHBatch01ContourInputI00.row00.drop 64).take 16)=true ∧
 ((RHBatch01ContourInputR00.row00.drop 64).take 16).length=16 := by decide +kernel
theorem checked00_05 : check v 80
 ((RHBatch01ContourInputR00.row00.drop 80).take 16) ((RHBatch01ContourInputI00.row00.drop 80).take 16)=true ∧
 ((RHBatch01ContourInputR00.row00.drop 80).take 16).length=16 := by decide +kernel
theorem checked00_06 : check v 96
 ((RHBatch01ContourInputR00.row00.drop 96).take 16) ((RHBatch01ContourInputI00.row00.drop 96).take 16)=true ∧
 ((RHBatch01ContourInputR00.row00.drop 96).take 16).length=16 := by decide +kernel
theorem checked00_07 : check v 112
 ((RHBatch01ContourInputR00.row00.drop 112).take 16) ((RHBatch01ContourInputI00.row00.drop 112).take 16)=true ∧
 ((RHBatch01ContourInputR00.row00.drop 112).take 16).length=16 := by decide +kernel
theorem checked00_08 : check v 128
 ((RHBatch01ContourInputR00.row00.drop 128).take 16) ((RHBatch01ContourInputI00.row00.drop 128).take 16)=true ∧
 ((RHBatch01ContourInputR00.row00.drop 128).take 16).length=16 := by decide +kernel
theorem checked00_09 : check v 144
 ((RHBatch01ContourInputR00.row00.drop 144).take 16) ((RHBatch01ContourInputI00.row00.drop 144).take 16)=true ∧
 ((RHBatch01ContourInputR00.row00.drop 144).take 16).length=16 := by decide +kernel
theorem checked00_10 : check v 160
 ((RHBatch01ContourInputR00.row00.drop 160).take 16) ((RHBatch01ContourInputI00.row00.drop 160).take 16)=true ∧
 ((RHBatch01ContourInputR00.row00.drop 160).take 16).length=16 := by decide +kernel
theorem checked00_11 : check v 176
 ((RHBatch01ContourInputR00.row00.drop 176).take 16) ((RHBatch01ContourInputI00.row00.drop 176).take 16)=true ∧
 ((RHBatch01ContourInputR00.row00.drop 176).take 16).length=16 := by decide +kernel
theorem checked00_12 : check v 192
 ((RHBatch01ContourInputR00.row00.drop 192).take 16) ((RHBatch01ContourInputI00.row00.drop 192).take 16)=true ∧
 ((RHBatch01ContourInputR00.row00.drop 192).take 16).length=16 := by decide +kernel
theorem checked00_13 : check v 208
 ((RHBatch01ContourInputR00.row00.drop 208).take 16) ((RHBatch01ContourInputI00.row00.drop 208).take 16)=true ∧
 ((RHBatch01ContourInputR00.row00.drop 208).take 16).length=16 := by decide +kernel
theorem checked00_14 : check v 224
 ((RHBatch01ContourInputR00.row00.drop 224).take 16) ((RHBatch01ContourInputI00.row00.drop 224).take 16)=true ∧
 ((RHBatch01ContourInputR00.row00.drop 224).take 16).length=16 := by decide +kernel
theorem checked00_15 : check v 240
 ((RHBatch01ContourInputR00.row00.drop 240).take 16) ((RHBatch01ContourInputI00.row00.drop 240).take 16)=true ∧
 ((RHBatch01ContourInputR00.row00.drop 240).take 16).length=16 := by decide +kernel
theorem checked00_16 : check v 256
 ((RHBatch01ContourInputR00.row00.drop 256).take 16) ((RHBatch01ContourInputI00.row00.drop 256).take 16)=true ∧
 ((RHBatch01ContourInputR00.row00.drop 256).take 16).length=16 := by decide +kernel
theorem checked00_17 : check v 272
 ((RHBatch01ContourInputR00.row00.drop 272).take 16) ((RHBatch01ContourInputI00.row00.drop 272).take 16)=true ∧
 ((RHBatch01ContourInputR00.row00.drop 272).take 16).length=16 := by decide +kernel
theorem checked00_18 : check v 288
 ((RHBatch01ContourInputR00.row00.drop 288).take 16) ((RHBatch01ContourInputI00.row00.drop 288).take 16)=true ∧
 ((RHBatch01ContourInputR00.row00.drop 288).take 16).length=16 := by decide +kernel
theorem checked00_19 : check v 304
 ((RHBatch01ContourInputR00.row00.drop 304).take 16) ((RHBatch01ContourInputI00.row00.drop 304).take 16)=true ∧
 ((RHBatch01ContourInputR00.row00.drop 304).take 16).length=16 := by decide +kernel
theorem checked00_20 : check v 320
 ((RHBatch01ContourInputR00.row00.drop 320).take 16) ((RHBatch01ContourInputI00.row00.drop 320).take 16)=true ∧
 ((RHBatch01ContourInputR00.row00.drop 320).take 16).length=16 := by decide +kernel
theorem checked00_21 : check v 336
 ((RHBatch01ContourInputR00.row00.drop 336).take 16) ((RHBatch01ContourInputI00.row00.drop 336).take 16)=true ∧
 ((RHBatch01ContourInputR00.row00.drop 336).take 16).length=16 := by decide +kernel
theorem checked00_22 : check v 352
 ((RHBatch01ContourInputR00.row00.drop 352).take 16) ((RHBatch01ContourInputI00.row00.drop 352).take 16)=true ∧
 ((RHBatch01ContourInputR00.row00.drop 352).take 16).length=16 := by decide +kernel
theorem checked00_23 : check v 368
 ((RHBatch01ContourInputR00.row00.drop 368).take 16) ((RHBatch01ContourInputI00.row00.drop 368).take 16)=true ∧
 ((RHBatch01ContourInputR00.row00.drop 368).take 16).length=16 := by decide +kernel
theorem checked00_24 : check v 384
 ((RHBatch01ContourInputR00.row00.drop 384).take 16) ((RHBatch01ContourInputI00.row00.drop 384).take 16)=true ∧
 ((RHBatch01ContourInputR00.row00.drop 384).take 16).length=16 := by decide +kernel
theorem checked00_25 : check v 400
 ((RHBatch01ContourInputR00.row00.drop 400).take 16) ((RHBatch01ContourInputI00.row00.drop 400).take 16)=true ∧
 ((RHBatch01ContourInputR00.row00.drop 400).take 16).length=16 := by decide +kernel
theorem checked00_26 : check v 416
 ((RHBatch01ContourInputR00.row00.drop 416).take 16) ((RHBatch01ContourInputI00.row00.drop 416).take 16)=true ∧
 ((RHBatch01ContourInputR00.row00.drop 416).take 16).length=16 := by decide +kernel
theorem checked00_27 : check v 432
 ((RHBatch01ContourInputR00.row00.drop 432).take 16) ((RHBatch01ContourInputI00.row00.drop 432).take 16)=true ∧
 ((RHBatch01ContourInputR00.row00.drop 432).take 16).length=16 := by decide +kernel
theorem checked00_28 : check v 448
 ((RHBatch01ContourInputR00.row00.drop 448).take 16) ((RHBatch01ContourInputI00.row00.drop 448).take 16)=true ∧
 ((RHBatch01ContourInputR00.row00.drop 448).take 16).length=16 := by decide +kernel
theorem checked00_29 : check v 464
 ((RHBatch01ContourInputR00.row00.drop 464).take 16) ((RHBatch01ContourInputI00.row00.drop 464).take 16)=true ∧
 ((RHBatch01ContourInputR00.row00.drop 464).take 16).length=16 := by decide +kernel
theorem checked00_30 : check v 480
 ((RHBatch01ContourInputR00.row00.drop 480).take 16) ((RHBatch01ContourInputI00.row00.drop 480).take 16)=true ∧
 ((RHBatch01ContourInputR00.row00.drop 480).take 16).length=16 := by decide +kernel
theorem checked00_31 : check v 496
 ((RHBatch01ContourInputR00.row00.drop 496).take 16) ((RHBatch01ContourInputI00.row00.drop 496).take 16)=true ∧
 ((RHBatch01ContourInputR00.row00.drop 496).take 16).length=16 := by decide +kernel
theorem checked01_00 : check v 512
 ((RHBatch01ContourInputR00.row01.drop 0).take 16) ((RHBatch01ContourInputI00.row01.drop 0).take 16)=true ∧
 ((RHBatch01ContourInputR00.row01.drop 0).take 16).length=16 := by decide +kernel
theorem checked01_01 : check v 528
 ((RHBatch01ContourInputR00.row01.drop 16).take 16) ((RHBatch01ContourInputI00.row01.drop 16).take 16)=true ∧
 ((RHBatch01ContourInputR00.row01.drop 16).take 16).length=16 := by decide +kernel
theorem checked01_02 : check v 544
 ((RHBatch01ContourInputR00.row01.drop 32).take 16) ((RHBatch01ContourInputI00.row01.drop 32).take 16)=true ∧
 ((RHBatch01ContourInputR00.row01.drop 32).take 16).length=16 := by decide +kernel
theorem checked01_03 : check v 560
 ((RHBatch01ContourInputR00.row01.drop 48).take 16) ((RHBatch01ContourInputI00.row01.drop 48).take 16)=true ∧
 ((RHBatch01ContourInputR00.row01.drop 48).take 16).length=16 := by decide +kernel
theorem checked01_04 : check v 576
 ((RHBatch01ContourInputR00.row01.drop 64).take 16) ((RHBatch01ContourInputI00.row01.drop 64).take 16)=true ∧
 ((RHBatch01ContourInputR00.row01.drop 64).take 16).length=16 := by decide +kernel
theorem checked01_05 : check v 592
 ((RHBatch01ContourInputR00.row01.drop 80).take 16) ((RHBatch01ContourInputI00.row01.drop 80).take 16)=true ∧
 ((RHBatch01ContourInputR00.row01.drop 80).take 16).length=16 := by decide +kernel
theorem checked01_06 : check v 608
 ((RHBatch01ContourInputR00.row01.drop 96).take 16) ((RHBatch01ContourInputI00.row01.drop 96).take 16)=true ∧
 ((RHBatch01ContourInputR00.row01.drop 96).take 16).length=16 := by decide +kernel
theorem checked01_07 : check v 624
 ((RHBatch01ContourInputR00.row01.drop 112).take 16) ((RHBatch01ContourInputI00.row01.drop 112).take 16)=true ∧
 ((RHBatch01ContourInputR00.row01.drop 112).take 16).length=16 := by decide +kernel
theorem checked01_08 : check v 640
 ((RHBatch01ContourInputR00.row01.drop 128).take 16) ((RHBatch01ContourInputI00.row01.drop 128).take 16)=true ∧
 ((RHBatch01ContourInputR00.row01.drop 128).take 16).length=16 := by decide +kernel
theorem checked01_09 : check v 656
 ((RHBatch01ContourInputR00.row01.drop 144).take 16) ((RHBatch01ContourInputI00.row01.drop 144).take 16)=true ∧
 ((RHBatch01ContourInputR00.row01.drop 144).take 16).length=16 := by decide +kernel
theorem checked01_10 : check v 672
 ((RHBatch01ContourInputR00.row01.drop 160).take 16) ((RHBatch01ContourInputI00.row01.drop 160).take 16)=true ∧
 ((RHBatch01ContourInputR00.row01.drop 160).take 16).length=16 := by decide +kernel
theorem checked01_11 : check v 688
 ((RHBatch01ContourInputR00.row01.drop 176).take 16) ((RHBatch01ContourInputI00.row01.drop 176).take 16)=true ∧
 ((RHBatch01ContourInputR00.row01.drop 176).take 16).length=16 := by decide +kernel
theorem checked01_12 : check v 704
 ((RHBatch01ContourInputR00.row01.drop 192).take 16) ((RHBatch01ContourInputI00.row01.drop 192).take 16)=true ∧
 ((RHBatch01ContourInputR00.row01.drop 192).take 16).length=16 := by decide +kernel
theorem checked01_13 : check v 720
 ((RHBatch01ContourInputR00.row01.drop 208).take 16) ((RHBatch01ContourInputI00.row01.drop 208).take 16)=true ∧
 ((RHBatch01ContourInputR00.row01.drop 208).take 16).length=16 := by decide +kernel
theorem checked01_14 : check v 736
 ((RHBatch01ContourInputR00.row01.drop 224).take 16) ((RHBatch01ContourInputI00.row01.drop 224).take 16)=true ∧
 ((RHBatch01ContourInputR00.row01.drop 224).take 16).length=16 := by decide +kernel
theorem checked01_15 : check v 752
 ((RHBatch01ContourInputR00.row01.drop 240).take 16) ((RHBatch01ContourInputI00.row01.drop 240).take 16)=true ∧
 ((RHBatch01ContourInputR00.row01.drop 240).take 16).length=16 := by decide +kernel
theorem checked01_16 : check v 768
 ((RHBatch01ContourInputR00.row01.drop 256).take 16) ((RHBatch01ContourInputI00.row01.drop 256).take 16)=true ∧
 ((RHBatch01ContourInputR00.row01.drop 256).take 16).length=16 := by decide +kernel
theorem checked01_17 : check v 784
 ((RHBatch01ContourInputR00.row01.drop 272).take 16) ((RHBatch01ContourInputI00.row01.drop 272).take 16)=true ∧
 ((RHBatch01ContourInputR00.row01.drop 272).take 16).length=16 := by decide +kernel
theorem checked01_18 : check v 800
 ((RHBatch01ContourInputR00.row01.drop 288).take 16) ((RHBatch01ContourInputI00.row01.drop 288).take 16)=true ∧
 ((RHBatch01ContourInputR00.row01.drop 288).take 16).length=16 := by decide +kernel
theorem checked01_19 : check v 816
 ((RHBatch01ContourInputR00.row01.drop 304).take 16) ((RHBatch01ContourInputI00.row01.drop 304).take 16)=true ∧
 ((RHBatch01ContourInputR00.row01.drop 304).take 16).length=16 := by decide +kernel
theorem checked01_20 : check v 832
 ((RHBatch01ContourInputR00.row01.drop 320).take 16) ((RHBatch01ContourInputI00.row01.drop 320).take 16)=true ∧
 ((RHBatch01ContourInputR00.row01.drop 320).take 16).length=16 := by decide +kernel
theorem checked01_21 : check v 848
 ((RHBatch01ContourInputR00.row01.drop 336).take 16) ((RHBatch01ContourInputI00.row01.drop 336).take 16)=true ∧
 ((RHBatch01ContourInputR00.row01.drop 336).take 16).length=16 := by decide +kernel
theorem checked01_22 : check v 864
 ((RHBatch01ContourInputR00.row01.drop 352).take 16) ((RHBatch01ContourInputI00.row01.drop 352).take 16)=true ∧
 ((RHBatch01ContourInputR00.row01.drop 352).take 16).length=16 := by decide +kernel
theorem checked01_23 : check v 880
 ((RHBatch01ContourInputR00.row01.drop 368).take 16) ((RHBatch01ContourInputI00.row01.drop 368).take 16)=true ∧
 ((RHBatch01ContourInputR00.row01.drop 368).take 16).length=16 := by decide +kernel
theorem checked01_24 : check v 896
 ((RHBatch01ContourInputR00.row01.drop 384).take 16) ((RHBatch01ContourInputI00.row01.drop 384).take 16)=true ∧
 ((RHBatch01ContourInputR00.row01.drop 384).take 16).length=16 := by decide +kernel
theorem checked01_25 : check v 912
 ((RHBatch01ContourInputR00.row01.drop 400).take 16) ((RHBatch01ContourInputI00.row01.drop 400).take 16)=true ∧
 ((RHBatch01ContourInputR00.row01.drop 400).take 16).length=16 := by decide +kernel
theorem checked01_26 : check v 928
 ((RHBatch01ContourInputR00.row01.drop 416).take 16) ((RHBatch01ContourInputI00.row01.drop 416).take 16)=true ∧
 ((RHBatch01ContourInputR00.row01.drop 416).take 16).length=16 := by decide +kernel
theorem checked01_27 : check v 944
 ((RHBatch01ContourInputR00.row01.drop 432).take 16) ((RHBatch01ContourInputI00.row01.drop 432).take 16)=true ∧
 ((RHBatch01ContourInputR00.row01.drop 432).take 16).length=16 := by decide +kernel
theorem checked01_28 : check v 960
 ((RHBatch01ContourInputR00.row01.drop 448).take 16) ((RHBatch01ContourInputI00.row01.drop 448).take 16)=true ∧
 ((RHBatch01ContourInputR00.row01.drop 448).take 16).length=16 := by decide +kernel
theorem checked01_29 : check v 976
 ((RHBatch01ContourInputR00.row01.drop 464).take 16) ((RHBatch01ContourInputI00.row01.drop 464).take 16)=true ∧
 ((RHBatch01ContourInputR00.row01.drop 464).take 16).length=16 := by decide +kernel
theorem checked01_30 : check v 992
 ((RHBatch01ContourInputR00.row01.drop 480).take 16) ((RHBatch01ContourInputI00.row01.drop 480).take 16)=true ∧
 ((RHBatch01ContourInputR00.row01.drop 480).take 16).length=16 := by decide +kernel
theorem checked01_31 : check v 1008
 ((RHBatch01ContourInputR00.row01.drop 496).take 16) ((RHBatch01ContourInputI00.row01.drop 496).take 16)=true ∧
 ((RHBatch01ContourInputR00.row01.drop 496).take 16).length=16 := by decide +kernel
theorem checked02_00 : check v 1024
 ((RHBatch01ContourInputR00.row02.drop 0).take 16) ((RHBatch01ContourInputI00.row02.drop 0).take 16)=true ∧
 ((RHBatch01ContourInputR00.row02.drop 0).take 16).length=16 := by decide +kernel
theorem checked02_01 : check v 1040
 ((RHBatch01ContourInputR00.row02.drop 16).take 16) ((RHBatch01ContourInputI00.row02.drop 16).take 16)=true ∧
 ((RHBatch01ContourInputR00.row02.drop 16).take 16).length=16 := by decide +kernel
theorem checked02_02 : check v 1056
 ((RHBatch01ContourInputR00.row02.drop 32).take 16) ((RHBatch01ContourInputI00.row02.drop 32).take 16)=true ∧
 ((RHBatch01ContourInputR00.row02.drop 32).take 16).length=16 := by decide +kernel
theorem checked02_03 : check v 1072
 ((RHBatch01ContourInputR00.row02.drop 48).take 16) ((RHBatch01ContourInputI00.row02.drop 48).take 16)=true ∧
 ((RHBatch01ContourInputR00.row02.drop 48).take 16).length=16 := by decide +kernel
theorem checked02_04 : check v 1088
 ((RHBatch01ContourInputR00.row02.drop 64).take 16) ((RHBatch01ContourInputI00.row02.drop 64).take 16)=true ∧
 ((RHBatch01ContourInputR00.row02.drop 64).take 16).length=16 := by decide +kernel
theorem checked02_05 : check v 1104
 ((RHBatch01ContourInputR00.row02.drop 80).take 16) ((RHBatch01ContourInputI00.row02.drop 80).take 16)=true ∧
 ((RHBatch01ContourInputR00.row02.drop 80).take 16).length=16 := by decide +kernel
theorem checked02_06 : check v 1120
 ((RHBatch01ContourInputR00.row02.drop 96).take 16) ((RHBatch01ContourInputI00.row02.drop 96).take 16)=true ∧
 ((RHBatch01ContourInputR00.row02.drop 96).take 16).length=16 := by decide +kernel
theorem checked02_07 : check v 1136
 ((RHBatch01ContourInputR00.row02.drop 112).take 16) ((RHBatch01ContourInputI00.row02.drop 112).take 16)=true ∧
 ((RHBatch01ContourInputR00.row02.drop 112).take 16).length=16 := by decide +kernel
theorem checked02_08 : check v 1152
 ((RHBatch01ContourInputR00.row02.drop 128).take 16) ((RHBatch01ContourInputI00.row02.drop 128).take 16)=true ∧
 ((RHBatch01ContourInputR00.row02.drop 128).take 16).length=16 := by decide +kernel
theorem checked02_09 : check v 1168
 ((RHBatch01ContourInputR00.row02.drop 144).take 16) ((RHBatch01ContourInputI00.row02.drop 144).take 16)=true ∧
 ((RHBatch01ContourInputR00.row02.drop 144).take 16).length=16 := by decide +kernel
theorem checked02_10 : check v 1184
 ((RHBatch01ContourInputR00.row02.drop 160).take 16) ((RHBatch01ContourInputI00.row02.drop 160).take 16)=true ∧
 ((RHBatch01ContourInputR00.row02.drop 160).take 16).length=16 := by decide +kernel
theorem checked02_11 : check v 1200
 ((RHBatch01ContourInputR00.row02.drop 176).take 16) ((RHBatch01ContourInputI00.row02.drop 176).take 16)=true ∧
 ((RHBatch01ContourInputR00.row02.drop 176).take 16).length=16 := by decide +kernel
theorem checked02_12 : check v 1216
 ((RHBatch01ContourInputR00.row02.drop 192).take 16) ((RHBatch01ContourInputI00.row02.drop 192).take 16)=true ∧
 ((RHBatch01ContourInputR00.row02.drop 192).take 16).length=16 := by decide +kernel
theorem checked02_13 : check v 1232
 ((RHBatch01ContourInputR00.row02.drop 208).take 16) ((RHBatch01ContourInputI00.row02.drop 208).take 16)=true ∧
 ((RHBatch01ContourInputR00.row02.drop 208).take 16).length=16 := by decide +kernel
theorem checked02_14 : check v 1248
 ((RHBatch01ContourInputR00.row02.drop 224).take 16) ((RHBatch01ContourInputI00.row02.drop 224).take 16)=true ∧
 ((RHBatch01ContourInputR00.row02.drop 224).take 16).length=16 := by decide +kernel
theorem checked02_15 : check v 1264
 ((RHBatch01ContourInputR00.row02.drop 240).take 16) ((RHBatch01ContourInputI00.row02.drop 240).take 16)=true ∧
 ((RHBatch01ContourInputR00.row02.drop 240).take 16).length=16 := by decide +kernel
theorem checked02_16 : check v 1280
 ((RHBatch01ContourInputR00.row02.drop 256).take 16) ((RHBatch01ContourInputI00.row02.drop 256).take 16)=true ∧
 ((RHBatch01ContourInputR00.row02.drop 256).take 16).length=16 := by decide +kernel
theorem checked02_17 : check v 1296
 ((RHBatch01ContourInputR00.row02.drop 272).take 16) ((RHBatch01ContourInputI00.row02.drop 272).take 16)=true ∧
 ((RHBatch01ContourInputR00.row02.drop 272).take 16).length=16 := by decide +kernel
theorem checked02_18 : check v 1312
 ((RHBatch01ContourInputR00.row02.drop 288).take 16) ((RHBatch01ContourInputI00.row02.drop 288).take 16)=true ∧
 ((RHBatch01ContourInputR00.row02.drop 288).take 16).length=16 := by decide +kernel
theorem checked02_19 : check v 1328
 ((RHBatch01ContourInputR00.row02.drop 304).take 16) ((RHBatch01ContourInputI00.row02.drop 304).take 16)=true ∧
 ((RHBatch01ContourInputR00.row02.drop 304).take 16).length=16 := by decide +kernel
theorem checked02_20 : check v 1344
 ((RHBatch01ContourInputR00.row02.drop 320).take 16) ((RHBatch01ContourInputI00.row02.drop 320).take 16)=true ∧
 ((RHBatch01ContourInputR00.row02.drop 320).take 16).length=16 := by decide +kernel
theorem checked02_21 : check v 1360
 ((RHBatch01ContourInputR00.row02.drop 336).take 16) ((RHBatch01ContourInputI00.row02.drop 336).take 16)=true ∧
 ((RHBatch01ContourInputR00.row02.drop 336).take 16).length=16 := by decide +kernel
theorem checked02_22 : check v 1376
 ((RHBatch01ContourInputR00.row02.drop 352).take 16) ((RHBatch01ContourInputI00.row02.drop 352).take 16)=true ∧
 ((RHBatch01ContourInputR00.row02.drop 352).take 16).length=16 := by decide +kernel
theorem checked02_23 : check v 1392
 ((RHBatch01ContourInputR00.row02.drop 368).take 16) ((RHBatch01ContourInputI00.row02.drop 368).take 16)=true ∧
 ((RHBatch01ContourInputR00.row02.drop 368).take 16).length=16 := by decide +kernel
theorem checked02_24 : check v 1408
 ((RHBatch01ContourInputR00.row02.drop 384).take 16) ((RHBatch01ContourInputI00.row02.drop 384).take 16)=true ∧
 ((RHBatch01ContourInputR00.row02.drop 384).take 16).length=16 := by decide +kernel
theorem checked02_25 : check v 1424
 ((RHBatch01ContourInputR00.row02.drop 400).take 16) ((RHBatch01ContourInputI00.row02.drop 400).take 16)=true ∧
 ((RHBatch01ContourInputR00.row02.drop 400).take 16).length=16 := by decide +kernel
theorem checked02_26 : check v 1440
 ((RHBatch01ContourInputR00.row02.drop 416).take 16) ((RHBatch01ContourInputI00.row02.drop 416).take 16)=true ∧
 ((RHBatch01ContourInputR00.row02.drop 416).take 16).length=16 := by decide +kernel
theorem checked02_27 : check v 1456
 ((RHBatch01ContourInputR00.row02.drop 432).take 16) ((RHBatch01ContourInputI00.row02.drop 432).take 16)=true ∧
 ((RHBatch01ContourInputR00.row02.drop 432).take 16).length=16 := by decide +kernel
theorem checked02_28 : check v 1472
 ((RHBatch01ContourInputR00.row02.drop 448).take 16) ((RHBatch01ContourInputI00.row02.drop 448).take 16)=true ∧
 ((RHBatch01ContourInputR00.row02.drop 448).take 16).length=16 := by decide +kernel
theorem checked02_29 : check v 1488
 ((RHBatch01ContourInputR00.row02.drop 464).take 16) ((RHBatch01ContourInputI00.row02.drop 464).take 16)=true ∧
 ((RHBatch01ContourInputR00.row02.drop 464).take 16).length=16 := by decide +kernel
theorem checked02_30 : check v 1504
 ((RHBatch01ContourInputR00.row02.drop 480).take 16) ((RHBatch01ContourInputI00.row02.drop 480).take 16)=true ∧
 ((RHBatch01ContourInputR00.row02.drop 480).take 16).length=16 := by decide +kernel
theorem checked02_31 : check v 1520
 ((RHBatch01ContourInputR00.row02.drop 496).take 16) ((RHBatch01ContourInputI00.row02.drop 496).take 16)=true ∧
 ((RHBatch01ContourInputR00.row02.drop 496).take 16).length=16 := by decide +kernel
theorem checked03_00 : check v 1536
 ((RHBatch01ContourInputR00.row03.drop 0).take 16) ((RHBatch01ContourInputI00.row03.drop 0).take 16)=true ∧
 ((RHBatch01ContourInputR00.row03.drop 0).take 16).length=16 := by decide +kernel
theorem checked03_01 : check v 1552
 ((RHBatch01ContourInputR00.row03.drop 16).take 16) ((RHBatch01ContourInputI00.row03.drop 16).take 16)=true ∧
 ((RHBatch01ContourInputR00.row03.drop 16).take 16).length=16 := by decide +kernel
theorem checked03_02 : check v 1568
 ((RHBatch01ContourInputR00.row03.drop 32).take 16) ((RHBatch01ContourInputI00.row03.drop 32).take 16)=true ∧
 ((RHBatch01ContourInputR00.row03.drop 32).take 16).length=16 := by decide +kernel
theorem checked03_03 : check v 1584
 ((RHBatch01ContourInputR00.row03.drop 48).take 16) ((RHBatch01ContourInputI00.row03.drop 48).take 16)=true ∧
 ((RHBatch01ContourInputR00.row03.drop 48).take 16).length=16 := by decide +kernel
theorem checked03_04 : check v 1600
 ((RHBatch01ContourInputR00.row03.drop 64).take 16) ((RHBatch01ContourInputI00.row03.drop 64).take 16)=true ∧
 ((RHBatch01ContourInputR00.row03.drop 64).take 16).length=16 := by decide +kernel
theorem checked03_05 : check v 1616
 ((RHBatch01ContourInputR00.row03.drop 80).take 16) ((RHBatch01ContourInputI00.row03.drop 80).take 16)=true ∧
 ((RHBatch01ContourInputR00.row03.drop 80).take 16).length=16 := by decide +kernel
theorem checked03_06 : check v 1632
 ((RHBatch01ContourInputR00.row03.drop 96).take 16) ((RHBatch01ContourInputI00.row03.drop 96).take 16)=true ∧
 ((RHBatch01ContourInputR00.row03.drop 96).take 16).length=16 := by decide +kernel
theorem checked03_07 : check v 1648
 ((RHBatch01ContourInputR00.row03.drop 112).take 16) ((RHBatch01ContourInputI00.row03.drop 112).take 16)=true ∧
 ((RHBatch01ContourInputR00.row03.drop 112).take 16).length=16 := by decide +kernel
theorem checked03_08 : check v 1664
 ((RHBatch01ContourInputR00.row03.drop 128).take 16) ((RHBatch01ContourInputI00.row03.drop 128).take 16)=true ∧
 ((RHBatch01ContourInputR00.row03.drop 128).take 16).length=16 := by decide +kernel
theorem checked03_09 : check v 1680
 ((RHBatch01ContourInputR00.row03.drop 144).take 16) ((RHBatch01ContourInputI00.row03.drop 144).take 16)=true ∧
 ((RHBatch01ContourInputR00.row03.drop 144).take 16).length=16 := by decide +kernel
theorem checked03_10 : check v 1696
 ((RHBatch01ContourInputR00.row03.drop 160).take 16) ((RHBatch01ContourInputI00.row03.drop 160).take 16)=true ∧
 ((RHBatch01ContourInputR00.row03.drop 160).take 16).length=16 := by decide +kernel
theorem checked03_11 : check v 1712
 ((RHBatch01ContourInputR00.row03.drop 176).take 16) ((RHBatch01ContourInputI00.row03.drop 176).take 16)=true ∧
 ((RHBatch01ContourInputR00.row03.drop 176).take 16).length=16 := by decide +kernel
theorem checked03_12 : check v 1728
 ((RHBatch01ContourInputR00.row03.drop 192).take 16) ((RHBatch01ContourInputI00.row03.drop 192).take 16)=true ∧
 ((RHBatch01ContourInputR00.row03.drop 192).take 16).length=16 := by decide +kernel
theorem checked03_13 : check v 1744
 ((RHBatch01ContourInputR00.row03.drop 208).take 16) ((RHBatch01ContourInputI00.row03.drop 208).take 16)=true ∧
 ((RHBatch01ContourInputR00.row03.drop 208).take 16).length=16 := by decide +kernel
theorem checked03_14 : check v 1760
 ((RHBatch01ContourInputR00.row03.drop 224).take 16) ((RHBatch01ContourInputI00.row03.drop 224).take 16)=true ∧
 ((RHBatch01ContourInputR00.row03.drop 224).take 16).length=16 := by decide +kernel
theorem checked03_15 : check v 1776
 ((RHBatch01ContourInputR00.row03.drop 240).take 16) ((RHBatch01ContourInputI00.row03.drop 240).take 16)=true ∧
 ((RHBatch01ContourInputR00.row03.drop 240).take 16).length=16 := by decide +kernel
theorem checked03_16 : check v 1792
 ((RHBatch01ContourInputR00.row03.drop 256).take 16) ((RHBatch01ContourInputI00.row03.drop 256).take 16)=true ∧
 ((RHBatch01ContourInputR00.row03.drop 256).take 16).length=16 := by decide +kernel
theorem checked03_17 : check v 1808
 ((RHBatch01ContourInputR00.row03.drop 272).take 16) ((RHBatch01ContourInputI00.row03.drop 272).take 16)=true ∧
 ((RHBatch01ContourInputR00.row03.drop 272).take 16).length=16 := by decide +kernel
theorem checked03_18 : check v 1824
 ((RHBatch01ContourInputR00.row03.drop 288).take 16) ((RHBatch01ContourInputI00.row03.drop 288).take 16)=true ∧
 ((RHBatch01ContourInputR00.row03.drop 288).take 16).length=16 := by decide +kernel
theorem checked03_19 : check v 1840
 ((RHBatch01ContourInputR00.row03.drop 304).take 16) ((RHBatch01ContourInputI00.row03.drop 304).take 16)=true ∧
 ((RHBatch01ContourInputR00.row03.drop 304).take 16).length=16 := by decide +kernel
theorem checked03_20 : check v 1856
 ((RHBatch01ContourInputR00.row03.drop 320).take 16) ((RHBatch01ContourInputI00.row03.drop 320).take 16)=true ∧
 ((RHBatch01ContourInputR00.row03.drop 320).take 16).length=16 := by decide +kernel
theorem checked03_21 : check v 1872
 ((RHBatch01ContourInputR00.row03.drop 336).take 16) ((RHBatch01ContourInputI00.row03.drop 336).take 16)=true ∧
 ((RHBatch01ContourInputR00.row03.drop 336).take 16).length=16 := by decide +kernel
theorem checked03_22 : check v 1888
 ((RHBatch01ContourInputR00.row03.drop 352).take 16) ((RHBatch01ContourInputI00.row03.drop 352).take 16)=true ∧
 ((RHBatch01ContourInputR00.row03.drop 352).take 16).length=16 := by decide +kernel
theorem checked03_23 : check v 1904
 ((RHBatch01ContourInputR00.row03.drop 368).take 16) ((RHBatch01ContourInputI00.row03.drop 368).take 16)=true ∧
 ((RHBatch01ContourInputR00.row03.drop 368).take 16).length=16 := by decide +kernel
theorem checked03_24 : check v 1920
 ((RHBatch01ContourInputR00.row03.drop 384).take 16) ((RHBatch01ContourInputI00.row03.drop 384).take 16)=true ∧
 ((RHBatch01ContourInputR00.row03.drop 384).take 16).length=16 := by decide +kernel
theorem checked03_25 : check v 1936
 ((RHBatch01ContourInputR00.row03.drop 400).take 16) ((RHBatch01ContourInputI00.row03.drop 400).take 16)=true ∧
 ((RHBatch01ContourInputR00.row03.drop 400).take 16).length=16 := by decide +kernel
theorem checked03_26 : check v 1952
 ((RHBatch01ContourInputR00.row03.drop 416).take 16) ((RHBatch01ContourInputI00.row03.drop 416).take 16)=true ∧
 ((RHBatch01ContourInputR00.row03.drop 416).take 16).length=16 := by decide +kernel
theorem checked03_27 : check v 1968
 ((RHBatch01ContourInputR00.row03.drop 432).take 16) ((RHBatch01ContourInputI00.row03.drop 432).take 16)=true ∧
 ((RHBatch01ContourInputR00.row03.drop 432).take 16).length=16 := by decide +kernel
theorem checked03_28 : check v 1984
 ((RHBatch01ContourInputR00.row03.drop 448).take 16) ((RHBatch01ContourInputI00.row03.drop 448).take 16)=true ∧
 ((RHBatch01ContourInputR00.row03.drop 448).take 16).length=16 := by decide +kernel
theorem checked03_29 : check v 2000
 ((RHBatch01ContourInputR00.row03.drop 464).take 16) ((RHBatch01ContourInputI00.row03.drop 464).take 16)=true ∧
 ((RHBatch01ContourInputR00.row03.drop 464).take 16).length=16 := by decide +kernel
theorem checked03_30 : check v 2016
 ((RHBatch01ContourInputR00.row03.drop 480).take 16) ((RHBatch01ContourInputI00.row03.drop 480).take 16)=true ∧
 ((RHBatch01ContourInputR00.row03.drop 480).take 16).length=16 := by decide +kernel
theorem checked03_31 : check v 2032
 ((RHBatch01ContourInputR00.row03.drop 496).take 16) ((RHBatch01ContourInputI00.row03.drop 496).take 16)=true ∧
 ((RHBatch01ContourInputR00.row03.drop 496).take 16).length=16 := by decide +kernel
theorem checked04_00 : check v 2048
 ((RHBatch01ContourInputR00.row04.drop 0).take 16) ((RHBatch01ContourInputI00.row04.drop 0).take 16)=true ∧
 ((RHBatch01ContourInputR00.row04.drop 0).take 16).length=16 := by decide +kernel
theorem checked04_01 : check v 2064
 ((RHBatch01ContourInputR00.row04.drop 16).take 16) ((RHBatch01ContourInputI00.row04.drop 16).take 16)=true ∧
 ((RHBatch01ContourInputR00.row04.drop 16).take 16).length=16 := by decide +kernel
theorem checked04_02 : check v 2080
 ((RHBatch01ContourInputR00.row04.drop 32).take 16) ((RHBatch01ContourInputI00.row04.drop 32).take 16)=true ∧
 ((RHBatch01ContourInputR00.row04.drop 32).take 16).length=16 := by decide +kernel
theorem checked04_03 : check v 2096
 ((RHBatch01ContourInputR00.row04.drop 48).take 16) ((RHBatch01ContourInputI00.row04.drop 48).take 16)=true ∧
 ((RHBatch01ContourInputR00.row04.drop 48).take 16).length=16 := by decide +kernel
theorem checked04_04 : check v 2112
 ((RHBatch01ContourInputR00.row04.drop 64).take 16) ((RHBatch01ContourInputI00.row04.drop 64).take 16)=true ∧
 ((RHBatch01ContourInputR00.row04.drop 64).take 16).length=16 := by decide +kernel
theorem checked04_05 : check v 2128
 ((RHBatch01ContourInputR00.row04.drop 80).take 16) ((RHBatch01ContourInputI00.row04.drop 80).take 16)=true ∧
 ((RHBatch01ContourInputR00.row04.drop 80).take 16).length=16 := by decide +kernel
theorem checked04_06 : check v 2144
 ((RHBatch01ContourInputR00.row04.drop 96).take 16) ((RHBatch01ContourInputI00.row04.drop 96).take 16)=true ∧
 ((RHBatch01ContourInputR00.row04.drop 96).take 16).length=16 := by decide +kernel
theorem checked04_07 : check v 2160
 ((RHBatch01ContourInputR00.row04.drop 112).take 16) ((RHBatch01ContourInputI00.row04.drop 112).take 16)=true ∧
 ((RHBatch01ContourInputR00.row04.drop 112).take 16).length=16 := by decide +kernel
theorem checked04_08 : check v 2176
 ((RHBatch01ContourInputR00.row04.drop 128).take 16) ((RHBatch01ContourInputI00.row04.drop 128).take 16)=true ∧
 ((RHBatch01ContourInputR00.row04.drop 128).take 16).length=16 := by decide +kernel
theorem checked04_09 : check v 2192
 ((RHBatch01ContourInputR00.row04.drop 144).take 16) ((RHBatch01ContourInputI00.row04.drop 144).take 16)=true ∧
 ((RHBatch01ContourInputR00.row04.drop 144).take 16).length=16 := by decide +kernel
theorem checked04_10 : check v 2208
 ((RHBatch01ContourInputR00.row04.drop 160).take 16) ((RHBatch01ContourInputI00.row04.drop 160).take 16)=true ∧
 ((RHBatch01ContourInputR00.row04.drop 160).take 16).length=16 := by decide +kernel
theorem checked04_11 : check v 2224
 ((RHBatch01ContourInputR00.row04.drop 176).take 16) ((RHBatch01ContourInputI00.row04.drop 176).take 16)=true ∧
 ((RHBatch01ContourInputR00.row04.drop 176).take 16).length=16 := by decide +kernel
theorem checked04_12 : check v 2240
 ((RHBatch01ContourInputR00.row04.drop 192).take 16) ((RHBatch01ContourInputI00.row04.drop 192).take 16)=true ∧
 ((RHBatch01ContourInputR00.row04.drop 192).take 16).length=16 := by decide +kernel
theorem checked04_13 : check v 2256
 ((RHBatch01ContourInputR00.row04.drop 208).take 16) ((RHBatch01ContourInputI00.row04.drop 208).take 16)=true ∧
 ((RHBatch01ContourInputR00.row04.drop 208).take 16).length=16 := by decide +kernel
theorem checked04_14 : check v 2272
 ((RHBatch01ContourInputR00.row04.drop 224).take 16) ((RHBatch01ContourInputI00.row04.drop 224).take 16)=true ∧
 ((RHBatch01ContourInputR00.row04.drop 224).take 16).length=16 := by decide +kernel
theorem checked04_15 : check v 2288
 ((RHBatch01ContourInputR00.row04.drop 240).take 16) ((RHBatch01ContourInputI00.row04.drop 240).take 16)=true ∧
 ((RHBatch01ContourInputR00.row04.drop 240).take 16).length=16 := by decide +kernel
theorem checked04_16 : check v 2304
 ((RHBatch01ContourInputR00.row04.drop 256).take 16) ((RHBatch01ContourInputI00.row04.drop 256).take 16)=true ∧
 ((RHBatch01ContourInputR00.row04.drop 256).take 16).length=16 := by decide +kernel
theorem checked04_17 : check v 2320
 ((RHBatch01ContourInputR00.row04.drop 272).take 16) ((RHBatch01ContourInputI00.row04.drop 272).take 16)=true ∧
 ((RHBatch01ContourInputR00.row04.drop 272).take 16).length=16 := by decide +kernel
theorem checked04_18 : check v 2336
 ((RHBatch01ContourInputR00.row04.drop 288).take 16) ((RHBatch01ContourInputI00.row04.drop 288).take 16)=true ∧
 ((RHBatch01ContourInputR00.row04.drop 288).take 16).length=16 := by decide +kernel
theorem checked04_19 : check v 2352
 ((RHBatch01ContourInputR00.row04.drop 304).take 16) ((RHBatch01ContourInputI00.row04.drop 304).take 16)=true ∧
 ((RHBatch01ContourInputR00.row04.drop 304).take 16).length=16 := by decide +kernel
theorem checked04_20 : check v 2368
 ((RHBatch01ContourInputR00.row04.drop 320).take 16) ((RHBatch01ContourInputI00.row04.drop 320).take 16)=true ∧
 ((RHBatch01ContourInputR00.row04.drop 320).take 16).length=16 := by decide +kernel
theorem checked04_21 : check v 2384
 ((RHBatch01ContourInputR00.row04.drop 336).take 16) ((RHBatch01ContourInputI00.row04.drop 336).take 16)=true ∧
 ((RHBatch01ContourInputR00.row04.drop 336).take 16).length=16 := by decide +kernel
theorem checked04_22 : check v 2400
 ((RHBatch01ContourInputR00.row04.drop 352).take 16) ((RHBatch01ContourInputI00.row04.drop 352).take 16)=true ∧
 ((RHBatch01ContourInputR00.row04.drop 352).take 16).length=16 := by decide +kernel
theorem checked04_23 : check v 2416
 ((RHBatch01ContourInputR00.row04.drop 368).take 16) ((RHBatch01ContourInputI00.row04.drop 368).take 16)=true ∧
 ((RHBatch01ContourInputR00.row04.drop 368).take 16).length=16 := by decide +kernel
theorem checked04_24 : check v 2432
 ((RHBatch01ContourInputR00.row04.drop 384).take 16) ((RHBatch01ContourInputI00.row04.drop 384).take 16)=true ∧
 ((RHBatch01ContourInputR00.row04.drop 384).take 16).length=16 := by decide +kernel
theorem checked04_25 : check v 2448
 ((RHBatch01ContourInputR00.row04.drop 400).take 16) ((RHBatch01ContourInputI00.row04.drop 400).take 16)=true ∧
 ((RHBatch01ContourInputR00.row04.drop 400).take 16).length=16 := by decide +kernel
theorem checked04_26 : check v 2464
 ((RHBatch01ContourInputR00.row04.drop 416).take 16) ((RHBatch01ContourInputI00.row04.drop 416).take 16)=true ∧
 ((RHBatch01ContourInputR00.row04.drop 416).take 16).length=16 := by decide +kernel
theorem checked04_27 : check v 2480
 ((RHBatch01ContourInputR00.row04.drop 432).take 16) ((RHBatch01ContourInputI00.row04.drop 432).take 16)=true ∧
 ((RHBatch01ContourInputR00.row04.drop 432).take 16).length=16 := by decide +kernel
theorem checked04_28 : check v 2496
 ((RHBatch01ContourInputR00.row04.drop 448).take 16) ((RHBatch01ContourInputI00.row04.drop 448).take 16)=true ∧
 ((RHBatch01ContourInputR00.row04.drop 448).take 16).length=16 := by decide +kernel
theorem checked04_29 : check v 2512
 ((RHBatch01ContourInputR00.row04.drop 464).take 16) ((RHBatch01ContourInputI00.row04.drop 464).take 16)=true ∧
 ((RHBatch01ContourInputR00.row04.drop 464).take 16).length=16 := by decide +kernel
theorem checked04_30 : check v 2528
 ((RHBatch01ContourInputR00.row04.drop 480).take 16) ((RHBatch01ContourInputI00.row04.drop 480).take 16)=true ∧
 ((RHBatch01ContourInputR00.row04.drop 480).take 16).length=16 := by decide +kernel
theorem checked04_31 : check v 2544
 ((RHBatch01ContourInputR00.row04.drop 496).take 16) ((RHBatch01ContourInputI00.row04.drop 496).take 16)=true ∧
 ((RHBatch01ContourInputR00.row04.drop 496).take 16).length=16 := by decide +kernel
theorem checked05_00 : check v 2560
 ((RHBatch01ContourInputR00.row05.drop 0).take 16) ((RHBatch01ContourInputI00.row05.drop 0).take 16)=true ∧
 ((RHBatch01ContourInputR00.row05.drop 0).take 16).length=16 := by decide +kernel
theorem checked05_01 : check v 2576
 ((RHBatch01ContourInputR00.row05.drop 16).take 16) ((RHBatch01ContourInputI00.row05.drop 16).take 16)=true ∧
 ((RHBatch01ContourInputR00.row05.drop 16).take 16).length=16 := by decide +kernel
theorem checked05_02 : check v 2592
 ((RHBatch01ContourInputR00.row05.drop 32).take 16) ((RHBatch01ContourInputI00.row05.drop 32).take 16)=true ∧
 ((RHBatch01ContourInputR00.row05.drop 32).take 16).length=16 := by decide +kernel
theorem checked05_03 : check v 2608
 ((RHBatch01ContourInputR00.row05.drop 48).take 16) ((RHBatch01ContourInputI00.row05.drop 48).take 16)=true ∧
 ((RHBatch01ContourInputR00.row05.drop 48).take 16).length=16 := by decide +kernel
theorem checked05_04 : check v 2624
 ((RHBatch01ContourInputR00.row05.drop 64).take 16) ((RHBatch01ContourInputI00.row05.drop 64).take 16)=true ∧
 ((RHBatch01ContourInputR00.row05.drop 64).take 16).length=16 := by decide +kernel
theorem checked05_05 : check v 2640
 ((RHBatch01ContourInputR00.row05.drop 80).take 16) ((RHBatch01ContourInputI00.row05.drop 80).take 16)=true ∧
 ((RHBatch01ContourInputR00.row05.drop 80).take 16).length=16 := by decide +kernel
theorem checked05_06 : check v 2656
 ((RHBatch01ContourInputR00.row05.drop 96).take 16) ((RHBatch01ContourInputI00.row05.drop 96).take 16)=true ∧
 ((RHBatch01ContourInputR00.row05.drop 96).take 16).length=16 := by decide +kernel
theorem checked05_07 : check v 2672
 ((RHBatch01ContourInputR00.row05.drop 112).take 16) ((RHBatch01ContourInputI00.row05.drop 112).take 16)=true ∧
 ((RHBatch01ContourInputR00.row05.drop 112).take 16).length=16 := by decide +kernel
theorem checked05_08 : check v 2688
 ((RHBatch01ContourInputR00.row05.drop 128).take 16) ((RHBatch01ContourInputI00.row05.drop 128).take 16)=true ∧
 ((RHBatch01ContourInputR00.row05.drop 128).take 16).length=16 := by decide +kernel
theorem checked05_09 : check v 2704
 ((RHBatch01ContourInputR00.row05.drop 144).take 16) ((RHBatch01ContourInputI00.row05.drop 144).take 16)=true ∧
 ((RHBatch01ContourInputR00.row05.drop 144).take 16).length=16 := by decide +kernel
theorem checked05_10 : check v 2720
 ((RHBatch01ContourInputR00.row05.drop 160).take 16) ((RHBatch01ContourInputI00.row05.drop 160).take 16)=true ∧
 ((RHBatch01ContourInputR00.row05.drop 160).take 16).length=16 := by decide +kernel
theorem checked05_11 : check v 2736
 ((RHBatch01ContourInputR00.row05.drop 176).take 16) ((RHBatch01ContourInputI00.row05.drop 176).take 16)=true ∧
 ((RHBatch01ContourInputR00.row05.drop 176).take 16).length=16 := by decide +kernel
theorem checked05_12 : check v 2752
 ((RHBatch01ContourInputR00.row05.drop 192).take 16) ((RHBatch01ContourInputI00.row05.drop 192).take 16)=true ∧
 ((RHBatch01ContourInputR00.row05.drop 192).take 16).length=16 := by decide +kernel
theorem checked05_13 : check v 2768
 ((RHBatch01ContourInputR00.row05.drop 208).take 16) ((RHBatch01ContourInputI00.row05.drop 208).take 16)=true ∧
 ((RHBatch01ContourInputR00.row05.drop 208).take 16).length=16 := by decide +kernel
theorem checked05_14 : check v 2784
 ((RHBatch01ContourInputR00.row05.drop 224).take 16) ((RHBatch01ContourInputI00.row05.drop 224).take 16)=true ∧
 ((RHBatch01ContourInputR00.row05.drop 224).take 16).length=16 := by decide +kernel
theorem checked05_15 : check v 2800
 ((RHBatch01ContourInputR00.row05.drop 240).take 16) ((RHBatch01ContourInputI00.row05.drop 240).take 16)=true ∧
 ((RHBatch01ContourInputR00.row05.drop 240).take 16).length=16 := by decide +kernel
theorem checked05_16 : check v 2816
 ((RHBatch01ContourInputR00.row05.drop 256).take 16) ((RHBatch01ContourInputI00.row05.drop 256).take 16)=true ∧
 ((RHBatch01ContourInputR00.row05.drop 256).take 16).length=16 := by decide +kernel
theorem checked05_17 : check v 2832
 ((RHBatch01ContourInputR00.row05.drop 272).take 16) ((RHBatch01ContourInputI00.row05.drop 272).take 16)=true ∧
 ((RHBatch01ContourInputR00.row05.drop 272).take 16).length=16 := by decide +kernel
theorem checked05_18 : check v 2848
 ((RHBatch01ContourInputR00.row05.drop 288).take 16) ((RHBatch01ContourInputI00.row05.drop 288).take 16)=true ∧
 ((RHBatch01ContourInputR00.row05.drop 288).take 16).length=16 := by decide +kernel
theorem checked05_19 : check v 2864
 ((RHBatch01ContourInputR00.row05.drop 304).take 16) ((RHBatch01ContourInputI00.row05.drop 304).take 16)=true ∧
 ((RHBatch01ContourInputR00.row05.drop 304).take 16).length=16 := by decide +kernel
theorem checked05_20 : check v 2880
 ((RHBatch01ContourInputR00.row05.drop 320).take 16) ((RHBatch01ContourInputI00.row05.drop 320).take 16)=true ∧
 ((RHBatch01ContourInputR00.row05.drop 320).take 16).length=16 := by decide +kernel
theorem checked05_21 : check v 2896
 ((RHBatch01ContourInputR00.row05.drop 336).take 16) ((RHBatch01ContourInputI00.row05.drop 336).take 16)=true ∧
 ((RHBatch01ContourInputR00.row05.drop 336).take 16).length=16 := by decide +kernel
theorem checked05_22 : check v 2912
 ((RHBatch01ContourInputR00.row05.drop 352).take 16) ((RHBatch01ContourInputI00.row05.drop 352).take 16)=true ∧
 ((RHBatch01ContourInputR00.row05.drop 352).take 16).length=16 := by decide +kernel
theorem checked05_23 : check v 2928
 ((RHBatch01ContourInputR00.row05.drop 368).take 16) ((RHBatch01ContourInputI00.row05.drop 368).take 16)=true ∧
 ((RHBatch01ContourInputR00.row05.drop 368).take 16).length=16 := by decide +kernel
theorem checked05_24 : check v 2944
 ((RHBatch01ContourInputR00.row05.drop 384).take 16) ((RHBatch01ContourInputI00.row05.drop 384).take 16)=true ∧
 ((RHBatch01ContourInputR00.row05.drop 384).take 16).length=16 := by decide +kernel
theorem checked05_25 : check v 2960
 ((RHBatch01ContourInputR00.row05.drop 400).take 16) ((RHBatch01ContourInputI00.row05.drop 400).take 16)=true ∧
 ((RHBatch01ContourInputR00.row05.drop 400).take 16).length=16 := by decide +kernel
theorem checked05_26 : check v 2976
 ((RHBatch01ContourInputR00.row05.drop 416).take 16) ((RHBatch01ContourInputI00.row05.drop 416).take 16)=true ∧
 ((RHBatch01ContourInputR00.row05.drop 416).take 16).length=16 := by decide +kernel
theorem checked05_27 : check v 2992
 ((RHBatch01ContourInputR00.row05.drop 432).take 16) ((RHBatch01ContourInputI00.row05.drop 432).take 16)=true ∧
 ((RHBatch01ContourInputR00.row05.drop 432).take 16).length=16 := by decide +kernel
theorem checked05_28 : check v 3008
 ((RHBatch01ContourInputR00.row05.drop 448).take 16) ((RHBatch01ContourInputI00.row05.drop 448).take 16)=true ∧
 ((RHBatch01ContourInputR00.row05.drop 448).take 16).length=16 := by decide +kernel
theorem checked05_29 : check v 3024
 ((RHBatch01ContourInputR00.row05.drop 464).take 16) ((RHBatch01ContourInputI00.row05.drop 464).take 16)=true ∧
 ((RHBatch01ContourInputR00.row05.drop 464).take 16).length=16 := by decide +kernel
theorem checked05_30 : check v 3040
 ((RHBatch01ContourInputR00.row05.drop 480).take 16) ((RHBatch01ContourInputI00.row05.drop 480).take 16)=true ∧
 ((RHBatch01ContourInputR00.row05.drop 480).take 16).length=16 := by decide +kernel
theorem checked05_31 : check v 3056
 ((RHBatch01ContourInputR00.row05.drop 496).take 16) ((RHBatch01ContourInputI00.row05.drop 496).take 16)=true ∧
 ((RHBatch01ContourInputR00.row05.drop 496).take 16).length=16 := by decide +kernel
theorem checked06_00 : check v 3072
 ((RHBatch01ContourInputR00.row06.drop 0).take 16) ((RHBatch01ContourInputI00.row06.drop 0).take 16)=true ∧
 ((RHBatch01ContourInputR00.row06.drop 0).take 16).length=16 := by decide +kernel
theorem checked06_01 : check v 3088
 ((RHBatch01ContourInputR00.row06.drop 16).take 16) ((RHBatch01ContourInputI00.row06.drop 16).take 16)=true ∧
 ((RHBatch01ContourInputR00.row06.drop 16).take 16).length=16 := by decide +kernel
theorem checked06_02 : check v 3104
 ((RHBatch01ContourInputR00.row06.drop 32).take 16) ((RHBatch01ContourInputI00.row06.drop 32).take 16)=true ∧
 ((RHBatch01ContourInputR00.row06.drop 32).take 16).length=16 := by decide +kernel
theorem checked06_03 : check v 3120
 ((RHBatch01ContourInputR00.row06.drop 48).take 16) ((RHBatch01ContourInputI00.row06.drop 48).take 16)=true ∧
 ((RHBatch01ContourInputR00.row06.drop 48).take 16).length=16 := by decide +kernel
theorem checked06_04 : check v 3136
 ((RHBatch01ContourInputR00.row06.drop 64).take 16) ((RHBatch01ContourInputI00.row06.drop 64).take 16)=true ∧
 ((RHBatch01ContourInputR00.row06.drop 64).take 16).length=16 := by decide +kernel
theorem checked06_05 : check v 3152
 ((RHBatch01ContourInputR00.row06.drop 80).take 16) ((RHBatch01ContourInputI00.row06.drop 80).take 16)=true ∧
 ((RHBatch01ContourInputR00.row06.drop 80).take 16).length=16 := by decide +kernel
theorem checked06_06 : check v 3168
 ((RHBatch01ContourInputR00.row06.drop 96).take 16) ((RHBatch01ContourInputI00.row06.drop 96).take 16)=true ∧
 ((RHBatch01ContourInputR00.row06.drop 96).take 16).length=16 := by decide +kernel
theorem checked06_07 : check v 3184
 ((RHBatch01ContourInputR00.row06.drop 112).take 16) ((RHBatch01ContourInputI00.row06.drop 112).take 16)=true ∧
 ((RHBatch01ContourInputR00.row06.drop 112).take 16).length=16 := by decide +kernel
theorem checked06_08 : check v 3200
 ((RHBatch01ContourInputR00.row06.drop 128).take 16) ((RHBatch01ContourInputI00.row06.drop 128).take 16)=true ∧
 ((RHBatch01ContourInputR00.row06.drop 128).take 16).length=16 := by decide +kernel
theorem checked06_09 : check v 3216
 ((RHBatch01ContourInputR00.row06.drop 144).take 16) ((RHBatch01ContourInputI00.row06.drop 144).take 16)=true ∧
 ((RHBatch01ContourInputR00.row06.drop 144).take 16).length=16 := by decide +kernel
theorem checked06_10 : check v 3232
 ((RHBatch01ContourInputR00.row06.drop 160).take 16) ((RHBatch01ContourInputI00.row06.drop 160).take 16)=true ∧
 ((RHBatch01ContourInputR00.row06.drop 160).take 16).length=16 := by decide +kernel
theorem checked06_11 : check v 3248
 ((RHBatch01ContourInputR00.row06.drop 176).take 16) ((RHBatch01ContourInputI00.row06.drop 176).take 16)=true ∧
 ((RHBatch01ContourInputR00.row06.drop 176).take 16).length=16 := by decide +kernel
theorem checked06_12 : check v 3264
 ((RHBatch01ContourInputR00.row06.drop 192).take 16) ((RHBatch01ContourInputI00.row06.drop 192).take 16)=true ∧
 ((RHBatch01ContourInputR00.row06.drop 192).take 16).length=16 := by decide +kernel
theorem checked06_13 : check v 3280
 ((RHBatch01ContourInputR00.row06.drop 208).take 16) ((RHBatch01ContourInputI00.row06.drop 208).take 16)=true ∧
 ((RHBatch01ContourInputR00.row06.drop 208).take 16).length=16 := by decide +kernel
theorem checked06_14 : check v 3296
 ((RHBatch01ContourInputR00.row06.drop 224).take 16) ((RHBatch01ContourInputI00.row06.drop 224).take 16)=true ∧
 ((RHBatch01ContourInputR00.row06.drop 224).take 16).length=16 := by decide +kernel
theorem checked06_15 : check v 3312
 ((RHBatch01ContourInputR00.row06.drop 240).take 16) ((RHBatch01ContourInputI00.row06.drop 240).take 16)=true ∧
 ((RHBatch01ContourInputR00.row06.drop 240).take 16).length=16 := by decide +kernel
theorem checked06_16 : check v 3328
 ((RHBatch01ContourInputR00.row06.drop 256).take 16) ((RHBatch01ContourInputI00.row06.drop 256).take 16)=true ∧
 ((RHBatch01ContourInputR00.row06.drop 256).take 16).length=16 := by decide +kernel
theorem checked06_17 : check v 3344
 ((RHBatch01ContourInputR00.row06.drop 272).take 16) ((RHBatch01ContourInputI00.row06.drop 272).take 16)=true ∧
 ((RHBatch01ContourInputR00.row06.drop 272).take 16).length=16 := by decide +kernel
theorem checked06_18 : check v 3360
 ((RHBatch01ContourInputR00.row06.drop 288).take 16) ((RHBatch01ContourInputI00.row06.drop 288).take 16)=true ∧
 ((RHBatch01ContourInputR00.row06.drop 288).take 16).length=16 := by decide +kernel
theorem checked06_19 : check v 3376
 ((RHBatch01ContourInputR00.row06.drop 304).take 16) ((RHBatch01ContourInputI00.row06.drop 304).take 16)=true ∧
 ((RHBatch01ContourInputR00.row06.drop 304).take 16).length=16 := by decide +kernel
theorem checked06_20 : check v 3392
 ((RHBatch01ContourInputR00.row06.drop 320).take 16) ((RHBatch01ContourInputI00.row06.drop 320).take 16)=true ∧
 ((RHBatch01ContourInputR00.row06.drop 320).take 16).length=16 := by decide +kernel
theorem checked06_21 : check v 3408
 ((RHBatch01ContourInputR00.row06.drop 336).take 16) ((RHBatch01ContourInputI00.row06.drop 336).take 16)=true ∧
 ((RHBatch01ContourInputR00.row06.drop 336).take 16).length=16 := by decide +kernel
theorem checked06_22 : check v 3424
 ((RHBatch01ContourInputR00.row06.drop 352).take 16) ((RHBatch01ContourInputI00.row06.drop 352).take 16)=true ∧
 ((RHBatch01ContourInputR00.row06.drop 352).take 16).length=16 := by decide +kernel
theorem checked06_23 : check v 3440
 ((RHBatch01ContourInputR00.row06.drop 368).take 16) ((RHBatch01ContourInputI00.row06.drop 368).take 16)=true ∧
 ((RHBatch01ContourInputR00.row06.drop 368).take 16).length=16 := by decide +kernel
theorem checked06_24 : check v 3456
 ((RHBatch01ContourInputR00.row06.drop 384).take 16) ((RHBatch01ContourInputI00.row06.drop 384).take 16)=true ∧
 ((RHBatch01ContourInputR00.row06.drop 384).take 16).length=16 := by decide +kernel
theorem checked06_25 : check v 3472
 ((RHBatch01ContourInputR00.row06.drop 400).take 16) ((RHBatch01ContourInputI00.row06.drop 400).take 16)=true ∧
 ((RHBatch01ContourInputR00.row06.drop 400).take 16).length=16 := by decide +kernel
theorem checked06_26 : check v 3488
 ((RHBatch01ContourInputR00.row06.drop 416).take 16) ((RHBatch01ContourInputI00.row06.drop 416).take 16)=true ∧
 ((RHBatch01ContourInputR00.row06.drop 416).take 16).length=16 := by decide +kernel
theorem checked06_27 : check v 3504
 ((RHBatch01ContourInputR00.row06.drop 432).take 16) ((RHBatch01ContourInputI00.row06.drop 432).take 16)=true ∧
 ((RHBatch01ContourInputR00.row06.drop 432).take 16).length=16 := by decide +kernel
theorem checked06_28 : check v 3520
 ((RHBatch01ContourInputR00.row06.drop 448).take 16) ((RHBatch01ContourInputI00.row06.drop 448).take 16)=true ∧
 ((RHBatch01ContourInputR00.row06.drop 448).take 16).length=16 := by decide +kernel
theorem checked06_29 : check v 3536
 ((RHBatch01ContourInputR00.row06.drop 464).take 16) ((RHBatch01ContourInputI00.row06.drop 464).take 16)=true ∧
 ((RHBatch01ContourInputR00.row06.drop 464).take 16).length=16 := by decide +kernel
theorem checked06_30 : check v 3552
 ((RHBatch01ContourInputR00.row06.drop 480).take 16) ((RHBatch01ContourInputI00.row06.drop 480).take 16)=true ∧
 ((RHBatch01ContourInputR00.row06.drop 480).take 16).length=16 := by decide +kernel
theorem checked06_31 : check v 3568
 ((RHBatch01ContourInputR00.row06.drop 496).take 16) ((RHBatch01ContourInputI00.row06.drop 496).take 16)=true ∧
 ((RHBatch01ContourInputR00.row06.drop 496).take 16).length=16 := by decide +kernel
theorem checked07_00 : check v 3584
 ((RHBatch01ContourInputR00.row07.drop 0).take 16) ((RHBatch01ContourInputI00.row07.drop 0).take 16)=true ∧
 ((RHBatch01ContourInputR00.row07.drop 0).take 16).length=16 := by decide +kernel
theorem checked07_01 : check v 3600
 ((RHBatch01ContourInputR00.row07.drop 16).take 16) ((RHBatch01ContourInputI00.row07.drop 16).take 16)=true ∧
 ((RHBatch01ContourInputR00.row07.drop 16).take 16).length=16 := by decide +kernel
theorem checked07_02 : check v 3616
 ((RHBatch01ContourInputR00.row07.drop 32).take 16) ((RHBatch01ContourInputI00.row07.drop 32).take 16)=true ∧
 ((RHBatch01ContourInputR00.row07.drop 32).take 16).length=16 := by decide +kernel
theorem checked07_03 : check v 3632
 ((RHBatch01ContourInputR00.row07.drop 48).take 16) ((RHBatch01ContourInputI00.row07.drop 48).take 16)=true ∧
 ((RHBatch01ContourInputR00.row07.drop 48).take 16).length=16 := by decide +kernel
theorem checked07_04 : check v 3648
 ((RHBatch01ContourInputR00.row07.drop 64).take 16) ((RHBatch01ContourInputI00.row07.drop 64).take 16)=true ∧
 ((RHBatch01ContourInputR00.row07.drop 64).take 16).length=16 := by decide +kernel
theorem checked07_05 : check v 3664
 ((RHBatch01ContourInputR00.row07.drop 80).take 16) ((RHBatch01ContourInputI00.row07.drop 80).take 16)=true ∧
 ((RHBatch01ContourInputR00.row07.drop 80).take 16).length=16 := by decide +kernel
theorem checked07_06 : check v 3680
 ((RHBatch01ContourInputR00.row07.drop 96).take 16) ((RHBatch01ContourInputI00.row07.drop 96).take 16)=true ∧
 ((RHBatch01ContourInputR00.row07.drop 96).take 16).length=16 := by decide +kernel
theorem checked07_07 : check v 3696
 ((RHBatch01ContourInputR00.row07.drop 112).take 16) ((RHBatch01ContourInputI00.row07.drop 112).take 16)=true ∧
 ((RHBatch01ContourInputR00.row07.drop 112).take 16).length=16 := by decide +kernel
theorem checked07_08 : check v 3712
 ((RHBatch01ContourInputR00.row07.drop 128).take 16) ((RHBatch01ContourInputI00.row07.drop 128).take 16)=true ∧
 ((RHBatch01ContourInputR00.row07.drop 128).take 16).length=16 := by decide +kernel
theorem checked07_09 : check v 3728
 ((RHBatch01ContourInputR00.row07.drop 144).take 16) ((RHBatch01ContourInputI00.row07.drop 144).take 16)=true ∧
 ((RHBatch01ContourInputR00.row07.drop 144).take 16).length=16 := by decide +kernel
theorem checked07_10 : check v 3744
 ((RHBatch01ContourInputR00.row07.drop 160).take 16) ((RHBatch01ContourInputI00.row07.drop 160).take 16)=true ∧
 ((RHBatch01ContourInputR00.row07.drop 160).take 16).length=16 := by decide +kernel
theorem checked07_11 : check v 3760
 ((RHBatch01ContourInputR00.row07.drop 176).take 16) ((RHBatch01ContourInputI00.row07.drop 176).take 16)=true ∧
 ((RHBatch01ContourInputR00.row07.drop 176).take 16).length=16 := by decide +kernel
theorem checked07_12 : check v 3776
 ((RHBatch01ContourInputR00.row07.drop 192).take 16) ((RHBatch01ContourInputI00.row07.drop 192).take 16)=true ∧
 ((RHBatch01ContourInputR00.row07.drop 192).take 16).length=16 := by decide +kernel
theorem checked07_13 : check v 3792
 ((RHBatch01ContourInputR00.row07.drop 208).take 16) ((RHBatch01ContourInputI00.row07.drop 208).take 16)=true ∧
 ((RHBatch01ContourInputR00.row07.drop 208).take 16).length=16 := by decide +kernel
theorem checked07_14 : check v 3808
 ((RHBatch01ContourInputR00.row07.drop 224).take 16) ((RHBatch01ContourInputI00.row07.drop 224).take 16)=true ∧
 ((RHBatch01ContourInputR00.row07.drop 224).take 16).length=16 := by decide +kernel
theorem checked07_15 : check v 3824
 ((RHBatch01ContourInputR00.row07.drop 240).take 16) ((RHBatch01ContourInputI00.row07.drop 240).take 16)=true ∧
 ((RHBatch01ContourInputR00.row07.drop 240).take 16).length=16 := by decide +kernel
theorem checked07_16 : check v 3840
 ((RHBatch01ContourInputR00.row07.drop 256).take 16) ((RHBatch01ContourInputI00.row07.drop 256).take 16)=true ∧
 ((RHBatch01ContourInputR00.row07.drop 256).take 16).length=16 := by decide +kernel
theorem checked07_17 : check v 3856
 ((RHBatch01ContourInputR00.row07.drop 272).take 16) ((RHBatch01ContourInputI00.row07.drop 272).take 16)=true ∧
 ((RHBatch01ContourInputR00.row07.drop 272).take 16).length=16 := by decide +kernel
theorem checked07_18 : check v 3872
 ((RHBatch01ContourInputR00.row07.drop 288).take 16) ((RHBatch01ContourInputI00.row07.drop 288).take 16)=true ∧
 ((RHBatch01ContourInputR00.row07.drop 288).take 16).length=16 := by decide +kernel
theorem checked07_19 : check v 3888
 ((RHBatch01ContourInputR00.row07.drop 304).take 16) ((RHBatch01ContourInputI00.row07.drop 304).take 16)=true ∧
 ((RHBatch01ContourInputR00.row07.drop 304).take 16).length=16 := by decide +kernel
theorem checked07_20 : check v 3904
 ((RHBatch01ContourInputR00.row07.drop 320).take 16) ((RHBatch01ContourInputI00.row07.drop 320).take 16)=true ∧
 ((RHBatch01ContourInputR00.row07.drop 320).take 16).length=16 := by decide +kernel
theorem checked07_21 : check v 3920
 ((RHBatch01ContourInputR00.row07.drop 336).take 16) ((RHBatch01ContourInputI00.row07.drop 336).take 16)=true ∧
 ((RHBatch01ContourInputR00.row07.drop 336).take 16).length=16 := by decide +kernel
theorem checked07_22 : check v 3936
 ((RHBatch01ContourInputR00.row07.drop 352).take 16) ((RHBatch01ContourInputI00.row07.drop 352).take 16)=true ∧
 ((RHBatch01ContourInputR00.row07.drop 352).take 16).length=16 := by decide +kernel
theorem checked07_23 : check v 3952
 ((RHBatch01ContourInputR00.row07.drop 368).take 16) ((RHBatch01ContourInputI00.row07.drop 368).take 16)=true ∧
 ((RHBatch01ContourInputR00.row07.drop 368).take 16).length=16 := by decide +kernel
theorem checked07_24 : check v 3968
 ((RHBatch01ContourInputR00.row07.drop 384).take 16) ((RHBatch01ContourInputI00.row07.drop 384).take 16)=true ∧
 ((RHBatch01ContourInputR00.row07.drop 384).take 16).length=16 := by decide +kernel
theorem checked07_25 : check v 3984
 ((RHBatch01ContourInputR00.row07.drop 400).take 16) ((RHBatch01ContourInputI00.row07.drop 400).take 16)=true ∧
 ((RHBatch01ContourInputR00.row07.drop 400).take 16).length=16 := by decide +kernel
theorem checked07_26 : check v 4000
 ((RHBatch01ContourInputR00.row07.drop 416).take 16) ((RHBatch01ContourInputI00.row07.drop 416).take 16)=true ∧
 ((RHBatch01ContourInputR00.row07.drop 416).take 16).length=16 := by decide +kernel
theorem checked07_27 : check v 4016
 ((RHBatch01ContourInputR00.row07.drop 432).take 16) ((RHBatch01ContourInputI00.row07.drop 432).take 16)=true ∧
 ((RHBatch01ContourInputR00.row07.drop 432).take 16).length=16 := by decide +kernel
theorem checked07_28 : check v 4032
 ((RHBatch01ContourInputR00.row07.drop 448).take 16) ((RHBatch01ContourInputI00.row07.drop 448).take 16)=true ∧
 ((RHBatch01ContourInputR00.row07.drop 448).take 16).length=16 := by decide +kernel
theorem checked07_29 : check v 4048
 ((RHBatch01ContourInputR00.row07.drop 464).take 16) ((RHBatch01ContourInputI00.row07.drop 464).take 16)=true ∧
 ((RHBatch01ContourInputR00.row07.drop 464).take 16).length=16 := by decide +kernel
theorem checked07_30 : check v 4064
 ((RHBatch01ContourInputR00.row07.drop 480).take 16) ((RHBatch01ContourInputI00.row07.drop 480).take 16)=true ∧
 ((RHBatch01ContourInputR00.row07.drop 480).take 16).length=16 := by decide +kernel
theorem checked07_31 : check v 4080
 ((RHBatch01ContourInputR00.row07.drop 496).take 16) ((RHBatch01ContourInputI00.row07.drop 496).take 16)=true ∧
 ((RHBatch01ContourInputR00.row07.drop 496).take 16).length=16 := by decide +kernel
theorem checked08_00 : check v 4096
 ((RHBatch01ContourInputR00.row08.drop 0).take 16) ((RHBatch01ContourInputI00.row08.drop 0).take 16)=true ∧
 ((RHBatch01ContourInputR00.row08.drop 0).take 16).length=16 := by decide +kernel
theorem checked08_01 : check v 4112
 ((RHBatch01ContourInputR00.row08.drop 16).take 16) ((RHBatch01ContourInputI00.row08.drop 16).take 16)=true ∧
 ((RHBatch01ContourInputR00.row08.drop 16).take 16).length=16 := by decide +kernel
theorem checked08_02 : check v 4128
 ((RHBatch01ContourInputR00.row08.drop 32).take 16) ((RHBatch01ContourInputI00.row08.drop 32).take 16)=true ∧
 ((RHBatch01ContourInputR00.row08.drop 32).take 16).length=16 := by decide +kernel
theorem checked08_03 : check v 4144
 ((RHBatch01ContourInputR00.row08.drop 48).take 16) ((RHBatch01ContourInputI00.row08.drop 48).take 16)=true ∧
 ((RHBatch01ContourInputR00.row08.drop 48).take 16).length=16 := by decide +kernel
theorem checked08_04 : check v 4160
 ((RHBatch01ContourInputR00.row08.drop 64).take 16) ((RHBatch01ContourInputI00.row08.drop 64).take 16)=true ∧
 ((RHBatch01ContourInputR00.row08.drop 64).take 16).length=16 := by decide +kernel
theorem checked08_05 : check v 4176
 ((RHBatch01ContourInputR00.row08.drop 80).take 16) ((RHBatch01ContourInputI00.row08.drop 80).take 16)=true ∧
 ((RHBatch01ContourInputR00.row08.drop 80).take 16).length=16 := by decide +kernel
theorem checked08_06 : check v 4192
 ((RHBatch01ContourInputR00.row08.drop 96).take 16) ((RHBatch01ContourInputI00.row08.drop 96).take 16)=true ∧
 ((RHBatch01ContourInputR00.row08.drop 96).take 16).length=16 := by decide +kernel
theorem checked08_07 : check v 4208
 ((RHBatch01ContourInputR00.row08.drop 112).take 16) ((RHBatch01ContourInputI00.row08.drop 112).take 16)=true ∧
 ((RHBatch01ContourInputR00.row08.drop 112).take 16).length=16 := by decide +kernel
theorem checked08_08 : check v 4224
 ((RHBatch01ContourInputR00.row08.drop 128).take 16) ((RHBatch01ContourInputI00.row08.drop 128).take 16)=true ∧
 ((RHBatch01ContourInputR00.row08.drop 128).take 16).length=16 := by decide +kernel
theorem checked08_09 : check v 4240
 ((RHBatch01ContourInputR00.row08.drop 144).take 16) ((RHBatch01ContourInputI00.row08.drop 144).take 16)=true ∧
 ((RHBatch01ContourInputR00.row08.drop 144).take 16).length=16 := by decide +kernel
theorem checked08_10 : check v 4256
 ((RHBatch01ContourInputR00.row08.drop 160).take 16) ((RHBatch01ContourInputI00.row08.drop 160).take 16)=true ∧
 ((RHBatch01ContourInputR00.row08.drop 160).take 16).length=16 := by decide +kernel
theorem checked08_11 : check v 4272
 ((RHBatch01ContourInputR00.row08.drop 176).take 16) ((RHBatch01ContourInputI00.row08.drop 176).take 16)=true ∧
 ((RHBatch01ContourInputR00.row08.drop 176).take 16).length=16 := by decide +kernel
theorem checked08_12 : check v 4288
 ((RHBatch01ContourInputR00.row08.drop 192).take 16) ((RHBatch01ContourInputI00.row08.drop 192).take 16)=true ∧
 ((RHBatch01ContourInputR00.row08.drop 192).take 16).length=16 := by decide +kernel
theorem checked08_13 : check v 4304
 ((RHBatch01ContourInputR00.row08.drop 208).take 16) ((RHBatch01ContourInputI00.row08.drop 208).take 16)=true ∧
 ((RHBatch01ContourInputR00.row08.drop 208).take 16).length=16 := by decide +kernel
theorem checked08_14 : check v 4320
 ((RHBatch01ContourInputR00.row08.drop 224).take 16) ((RHBatch01ContourInputI00.row08.drop 224).take 16)=true ∧
 ((RHBatch01ContourInputR00.row08.drop 224).take 16).length=16 := by decide +kernel
theorem checked08_15 : check v 4336
 ((RHBatch01ContourInputR00.row08.drop 240).take 16) ((RHBatch01ContourInputI00.row08.drop 240).take 16)=true ∧
 ((RHBatch01ContourInputR00.row08.drop 240).take 16).length=16 := by decide +kernel
theorem checked08_16 : check v 4352
 ((RHBatch01ContourInputR00.row08.drop 256).take 16) ((RHBatch01ContourInputI00.row08.drop 256).take 16)=true ∧
 ((RHBatch01ContourInputR00.row08.drop 256).take 16).length=16 := by decide +kernel
theorem checked08_17 : check v 4368
 ((RHBatch01ContourInputR00.row08.drop 272).take 16) ((RHBatch01ContourInputI00.row08.drop 272).take 16)=true ∧
 ((RHBatch01ContourInputR00.row08.drop 272).take 16).length=16 := by decide +kernel
theorem checked08_18 : check v 4384
 ((RHBatch01ContourInputR00.row08.drop 288).take 16) ((RHBatch01ContourInputI00.row08.drop 288).take 16)=true ∧
 ((RHBatch01ContourInputR00.row08.drop 288).take 16).length=16 := by decide +kernel
theorem checked08_19 : check v 4400
 ((RHBatch01ContourInputR00.row08.drop 304).take 16) ((RHBatch01ContourInputI00.row08.drop 304).take 16)=true ∧
 ((RHBatch01ContourInputR00.row08.drop 304).take 16).length=16 := by decide +kernel
theorem checked08_20 : check v 4416
 ((RHBatch01ContourInputR00.row08.drop 320).take 16) ((RHBatch01ContourInputI00.row08.drop 320).take 16)=true ∧
 ((RHBatch01ContourInputR00.row08.drop 320).take 16).length=16 := by decide +kernel
theorem checked08_21 : check v 4432
 ((RHBatch01ContourInputR00.row08.drop 336).take 16) ((RHBatch01ContourInputI00.row08.drop 336).take 16)=true ∧
 ((RHBatch01ContourInputR00.row08.drop 336).take 16).length=16 := by decide +kernel
theorem checked08_22 : check v 4448
 ((RHBatch01ContourInputR00.row08.drop 352).take 16) ((RHBatch01ContourInputI00.row08.drop 352).take 16)=true ∧
 ((RHBatch01ContourInputR00.row08.drop 352).take 16).length=16 := by decide +kernel
theorem checked08_23 : check v 4464
 ((RHBatch01ContourInputR00.row08.drop 368).take 16) ((RHBatch01ContourInputI00.row08.drop 368).take 16)=true ∧
 ((RHBatch01ContourInputR00.row08.drop 368).take 16).length=16 := by decide +kernel
theorem checked08_24 : check v 4480
 ((RHBatch01ContourInputR00.row08.drop 384).take 16) ((RHBatch01ContourInputI00.row08.drop 384).take 16)=true ∧
 ((RHBatch01ContourInputR00.row08.drop 384).take 16).length=16 := by decide +kernel
theorem checked08_25 : check v 4496
 ((RHBatch01ContourInputR00.row08.drop 400).take 16) ((RHBatch01ContourInputI00.row08.drop 400).take 16)=true ∧
 ((RHBatch01ContourInputR00.row08.drop 400).take 16).length=16 := by decide +kernel
theorem checked08_26 : check v 4512
 ((RHBatch01ContourInputR00.row08.drop 416).take 16) ((RHBatch01ContourInputI00.row08.drop 416).take 16)=true ∧
 ((RHBatch01ContourInputR00.row08.drop 416).take 16).length=16 := by decide +kernel
theorem checked08_27 : check v 4528
 ((RHBatch01ContourInputR00.row08.drop 432).take 16) ((RHBatch01ContourInputI00.row08.drop 432).take 16)=true ∧
 ((RHBatch01ContourInputR00.row08.drop 432).take 16).length=16 := by decide +kernel
theorem checked08_28 : check v 4544
 ((RHBatch01ContourInputR00.row08.drop 448).take 16) ((RHBatch01ContourInputI00.row08.drop 448).take 16)=true ∧
 ((RHBatch01ContourInputR00.row08.drop 448).take 16).length=16 := by decide +kernel
theorem checked08_29 : check v 4560
 ((RHBatch01ContourInputR00.row08.drop 464).take 16) ((RHBatch01ContourInputI00.row08.drop 464).take 16)=true ∧
 ((RHBatch01ContourInputR00.row08.drop 464).take 16).length=16 := by decide +kernel
theorem checked08_30 : check v 4576
 ((RHBatch01ContourInputR00.row08.drop 480).take 16) ((RHBatch01ContourInputI00.row08.drop 480).take 16)=true ∧
 ((RHBatch01ContourInputR00.row08.drop 480).take 16).length=16 := by decide +kernel
theorem checked08_31 : check v 4592
 ((RHBatch01ContourInputR00.row08.drop 496).take 16) ((RHBatch01ContourInputI00.row08.drop 496).take 16)=true ∧
 ((RHBatch01ContourInputR00.row08.drop 496).take 16).length=16 := by decide +kernel
theorem checked09_00 : check v 4608
 ((RHBatch01ContourInputR00.row09.drop 0).take 16) ((RHBatch01ContourInputI00.row09.drop 0).take 16)=true ∧
 ((RHBatch01ContourInputR00.row09.drop 0).take 16).length=16 := by decide +kernel
theorem checked09_01 : check v 4624
 ((RHBatch01ContourInputR00.row09.drop 16).take 16) ((RHBatch01ContourInputI00.row09.drop 16).take 16)=true ∧
 ((RHBatch01ContourInputR00.row09.drop 16).take 16).length=16 := by decide +kernel
theorem checked09_02 : check v 4640
 ((RHBatch01ContourInputR00.row09.drop 32).take 16) ((RHBatch01ContourInputI00.row09.drop 32).take 16)=true ∧
 ((RHBatch01ContourInputR00.row09.drop 32).take 16).length=16 := by decide +kernel
theorem checked09_03 : check v 4656
 ((RHBatch01ContourInputR00.row09.drop 48).take 16) ((RHBatch01ContourInputI00.row09.drop 48).take 16)=true ∧
 ((RHBatch01ContourInputR00.row09.drop 48).take 16).length=16 := by decide +kernel
theorem checked09_04 : check v 4672
 ((RHBatch01ContourInputR00.row09.drop 64).take 16) ((RHBatch01ContourInputI00.row09.drop 64).take 16)=true ∧
 ((RHBatch01ContourInputR00.row09.drop 64).take 16).length=16 := by decide +kernel
theorem checked09_05 : check v 4688
 ((RHBatch01ContourInputR00.row09.drop 80).take 16) ((RHBatch01ContourInputI00.row09.drop 80).take 16)=true ∧
 ((RHBatch01ContourInputR00.row09.drop 80).take 16).length=16 := by decide +kernel
theorem checked09_06 : check v 4704
 ((RHBatch01ContourInputR00.row09.drop 96).take 16) ((RHBatch01ContourInputI00.row09.drop 96).take 16)=true ∧
 ((RHBatch01ContourInputR00.row09.drop 96).take 16).length=16 := by decide +kernel
theorem checked09_07 : check v 4720
 ((RHBatch01ContourInputR00.row09.drop 112).take 16) ((RHBatch01ContourInputI00.row09.drop 112).take 16)=true ∧
 ((RHBatch01ContourInputR00.row09.drop 112).take 16).length=16 := by decide +kernel
theorem checked09_08 : check v 4736
 ((RHBatch01ContourInputR00.row09.drop 128).take 16) ((RHBatch01ContourInputI00.row09.drop 128).take 16)=true ∧
 ((RHBatch01ContourInputR00.row09.drop 128).take 16).length=16 := by decide +kernel
theorem checked09_09 : check v 4752
 ((RHBatch01ContourInputR00.row09.drop 144).take 16) ((RHBatch01ContourInputI00.row09.drop 144).take 16)=true ∧
 ((RHBatch01ContourInputR00.row09.drop 144).take 16).length=16 := by decide +kernel
theorem checked09_10 : check v 4768
 ((RHBatch01ContourInputR00.row09.drop 160).take 16) ((RHBatch01ContourInputI00.row09.drop 160).take 16)=true ∧
 ((RHBatch01ContourInputR00.row09.drop 160).take 16).length=16 := by decide +kernel
theorem checked09_11 : check v 4784
 ((RHBatch01ContourInputR00.row09.drop 176).take 16) ((RHBatch01ContourInputI00.row09.drop 176).take 16)=true ∧
 ((RHBatch01ContourInputR00.row09.drop 176).take 16).length=16 := by decide +kernel
theorem checked09_12 : check v 4800
 ((RHBatch01ContourInputR00.row09.drop 192).take 16) ((RHBatch01ContourInputI00.row09.drop 192).take 16)=true ∧
 ((RHBatch01ContourInputR00.row09.drop 192).take 16).length=16 := by decide +kernel
theorem checked09_13 : check v 4816
 ((RHBatch01ContourInputR00.row09.drop 208).take 16) ((RHBatch01ContourInputI00.row09.drop 208).take 16)=true ∧
 ((RHBatch01ContourInputR00.row09.drop 208).take 16).length=16 := by decide +kernel
theorem checked09_14 : check v 4832
 ((RHBatch01ContourInputR00.row09.drop 224).take 16) ((RHBatch01ContourInputI00.row09.drop 224).take 16)=true ∧
 ((RHBatch01ContourInputR00.row09.drop 224).take 16).length=16 := by decide +kernel
theorem checked09_15 : check v 4848
 ((RHBatch01ContourInputR00.row09.drop 240).take 16) ((RHBatch01ContourInputI00.row09.drop 240).take 16)=true ∧
 ((RHBatch01ContourInputR00.row09.drop 240).take 16).length=16 := by decide +kernel
theorem checked09_16 : check v 4864
 ((RHBatch01ContourInputR00.row09.drop 256).take 16) ((RHBatch01ContourInputI00.row09.drop 256).take 16)=true ∧
 ((RHBatch01ContourInputR00.row09.drop 256).take 16).length=16 := by decide +kernel
theorem checked09_17 : check v 4880
 ((RHBatch01ContourInputR00.row09.drop 272).take 16) ((RHBatch01ContourInputI00.row09.drop 272).take 16)=true ∧
 ((RHBatch01ContourInputR00.row09.drop 272).take 16).length=16 := by decide +kernel
theorem checked09_18 : check v 4896
 ((RHBatch01ContourInputR00.row09.drop 288).take 16) ((RHBatch01ContourInputI00.row09.drop 288).take 16)=true ∧
 ((RHBatch01ContourInputR00.row09.drop 288).take 16).length=16 := by decide +kernel
theorem checked09_19 : check v 4912
 ((RHBatch01ContourInputR00.row09.drop 304).take 16) ((RHBatch01ContourInputI00.row09.drop 304).take 16)=true ∧
 ((RHBatch01ContourInputR00.row09.drop 304).take 16).length=16 := by decide +kernel
theorem checked09_20 : check v 4928
 ((RHBatch01ContourInputR00.row09.drop 320).take 16) ((RHBatch01ContourInputI00.row09.drop 320).take 16)=true ∧
 ((RHBatch01ContourInputR00.row09.drop 320).take 16).length=16 := by decide +kernel
theorem checked09_21 : check v 4944
 ((RHBatch01ContourInputR00.row09.drop 336).take 16) ((RHBatch01ContourInputI00.row09.drop 336).take 16)=true ∧
 ((RHBatch01ContourInputR00.row09.drop 336).take 16).length=16 := by decide +kernel
theorem checked09_22 : check v 4960
 ((RHBatch01ContourInputR00.row09.drop 352).take 16) ((RHBatch01ContourInputI00.row09.drop 352).take 16)=true ∧
 ((RHBatch01ContourInputR00.row09.drop 352).take 16).length=16 := by decide +kernel
theorem checked09_23 : check v 4976
 ((RHBatch01ContourInputR00.row09.drop 368).take 16) ((RHBatch01ContourInputI00.row09.drop 368).take 16)=true ∧
 ((RHBatch01ContourInputR00.row09.drop 368).take 16).length=16 := by decide +kernel
theorem checked09_24 : check v 4992
 ((RHBatch01ContourInputR00.row09.drop 384).take 16) ((RHBatch01ContourInputI00.row09.drop 384).take 16)=true ∧
 ((RHBatch01ContourInputR00.row09.drop 384).take 16).length=16 := by decide +kernel
theorem checked09_25 : check v 5008
 ((RHBatch01ContourInputR00.row09.drop 400).take 16) ((RHBatch01ContourInputI00.row09.drop 400).take 16)=true ∧
 ((RHBatch01ContourInputR00.row09.drop 400).take 16).length=16 := by decide +kernel
theorem checked09_26 : check v 5024
 ((RHBatch01ContourInputR00.row09.drop 416).take 16) ((RHBatch01ContourInputI00.row09.drop 416).take 16)=true ∧
 ((RHBatch01ContourInputR00.row09.drop 416).take 16).length=16 := by decide +kernel
theorem checked09_27 : check v 5040
 ((RHBatch01ContourInputR00.row09.drop 432).take 16) ((RHBatch01ContourInputI00.row09.drop 432).take 16)=true ∧
 ((RHBatch01ContourInputR00.row09.drop 432).take 16).length=16 := by decide +kernel
theorem checked09_28 : check v 5056
 ((RHBatch01ContourInputR00.row09.drop 448).take 16) ((RHBatch01ContourInputI00.row09.drop 448).take 16)=true ∧
 ((RHBatch01ContourInputR00.row09.drop 448).take 16).length=16 := by decide +kernel
theorem checked09_29 : check v 5072
 ((RHBatch01ContourInputR00.row09.drop 464).take 16) ((RHBatch01ContourInputI00.row09.drop 464).take 16)=true ∧
 ((RHBatch01ContourInputR00.row09.drop 464).take 16).length=16 := by decide +kernel
theorem checked09_30 : check v 5088
 ((RHBatch01ContourInputR00.row09.drop 480).take 16) ((RHBatch01ContourInputI00.row09.drop 480).take 16)=true ∧
 ((RHBatch01ContourInputR00.row09.drop 480).take 16).length=16 := by decide +kernel
theorem checked09_31 : check v 5104
 ((RHBatch01ContourInputR00.row09.drop 496).take 16) ((RHBatch01ContourInputI00.row09.drop 496).take 16)=true ∧
 ((RHBatch01ContourInputR00.row09.drop 496).take 16).length=16 := by decide +kernel
theorem checked10_00 : check v 5120
 ((RHBatch01ContourInputR00.row10.drop 0).take 16) ((RHBatch01ContourInputI00.row10.drop 0).take 16)=true ∧
 ((RHBatch01ContourInputR00.row10.drop 0).take 16).length=16 := by decide +kernel
theorem checked10_01 : check v 5136
 ((RHBatch01ContourInputR00.row10.drop 16).take 16) ((RHBatch01ContourInputI00.row10.drop 16).take 16)=true ∧
 ((RHBatch01ContourInputR00.row10.drop 16).take 16).length=16 := by decide +kernel
theorem checked10_02 : check v 5152
 ((RHBatch01ContourInputR00.row10.drop 32).take 16) ((RHBatch01ContourInputI00.row10.drop 32).take 16)=true ∧
 ((RHBatch01ContourInputR00.row10.drop 32).take 16).length=16 := by decide +kernel
theorem checked10_03 : check v 5168
 ((RHBatch01ContourInputR00.row10.drop 48).take 16) ((RHBatch01ContourInputI00.row10.drop 48).take 16)=true ∧
 ((RHBatch01ContourInputR00.row10.drop 48).take 16).length=16 := by decide +kernel
theorem checked10_04 : check v 5184
 ((RHBatch01ContourInputR00.row10.drop 64).take 16) ((RHBatch01ContourInputI00.row10.drop 64).take 16)=true ∧
 ((RHBatch01ContourInputR00.row10.drop 64).take 16).length=16 := by decide +kernel
theorem checked10_05 : check v 5200
 ((RHBatch01ContourInputR00.row10.drop 80).take 16) ((RHBatch01ContourInputI00.row10.drop 80).take 16)=true ∧
 ((RHBatch01ContourInputR00.row10.drop 80).take 16).length=16 := by decide +kernel
theorem checked10_06 : check v 5216
 ((RHBatch01ContourInputR00.row10.drop 96).take 16) ((RHBatch01ContourInputI00.row10.drop 96).take 16)=true ∧
 ((RHBatch01ContourInputR00.row10.drop 96).take 16).length=16 := by decide +kernel
theorem checked10_07 : check v 5232
 ((RHBatch01ContourInputR00.row10.drop 112).take 16) ((RHBatch01ContourInputI00.row10.drop 112).take 16)=true ∧
 ((RHBatch01ContourInputR00.row10.drop 112).take 16).length=16 := by decide +kernel
theorem checked10_08 : check v 5248
 ((RHBatch01ContourInputR00.row10.drop 128).take 16) ((RHBatch01ContourInputI00.row10.drop 128).take 16)=true ∧
 ((RHBatch01ContourInputR00.row10.drop 128).take 16).length=16 := by decide +kernel
theorem checked10_09 : check v 5264
 ((RHBatch01ContourInputR00.row10.drop 144).take 16) ((RHBatch01ContourInputI00.row10.drop 144).take 16)=true ∧
 ((RHBatch01ContourInputR00.row10.drop 144).take 16).length=16 := by decide +kernel
theorem checked10_10 : check v 5280
 ((RHBatch01ContourInputR00.row10.drop 160).take 16) ((RHBatch01ContourInputI00.row10.drop 160).take 16)=true ∧
 ((RHBatch01ContourInputR00.row10.drop 160).take 16).length=16 := by decide +kernel
theorem checked10_11 : check v 5296
 ((RHBatch01ContourInputR00.row10.drop 176).take 16) ((RHBatch01ContourInputI00.row10.drop 176).take 16)=true ∧
 ((RHBatch01ContourInputR00.row10.drop 176).take 16).length=16 := by decide +kernel
theorem checked10_12 : check v 5312
 ((RHBatch01ContourInputR00.row10.drop 192).take 16) ((RHBatch01ContourInputI00.row10.drop 192).take 16)=true ∧
 ((RHBatch01ContourInputR00.row10.drop 192).take 16).length=16 := by decide +kernel
theorem checked10_13 : check v 5328
 ((RHBatch01ContourInputR00.row10.drop 208).take 16) ((RHBatch01ContourInputI00.row10.drop 208).take 16)=true ∧
 ((RHBatch01ContourInputR00.row10.drop 208).take 16).length=16 := by decide +kernel
theorem checked10_14 : check v 5344
 ((RHBatch01ContourInputR00.row10.drop 224).take 16) ((RHBatch01ContourInputI00.row10.drop 224).take 16)=true ∧
 ((RHBatch01ContourInputR00.row10.drop 224).take 16).length=16 := by decide +kernel
theorem checked10_15 : check v 5360
 ((RHBatch01ContourInputR00.row10.drop 240).take 16) ((RHBatch01ContourInputI00.row10.drop 240).take 16)=true ∧
 ((RHBatch01ContourInputR00.row10.drop 240).take 16).length=16 := by decide +kernel
theorem checked10_16 : check v 5376
 ((RHBatch01ContourInputR00.row10.drop 256).take 16) ((RHBatch01ContourInputI00.row10.drop 256).take 16)=true ∧
 ((RHBatch01ContourInputR00.row10.drop 256).take 16).length=16 := by decide +kernel
theorem checked10_17 : check v 5392
 ((RHBatch01ContourInputR00.row10.drop 272).take 16) ((RHBatch01ContourInputI00.row10.drop 272).take 16)=true ∧
 ((RHBatch01ContourInputR00.row10.drop 272).take 16).length=16 := by decide +kernel
theorem checked10_18 : check v 5408
 ((RHBatch01ContourInputR00.row10.drop 288).take 16) ((RHBatch01ContourInputI00.row10.drop 288).take 16)=true ∧
 ((RHBatch01ContourInputR00.row10.drop 288).take 16).length=16 := by decide +kernel
theorem checked10_19 : check v 5424
 ((RHBatch01ContourInputR00.row10.drop 304).take 16) ((RHBatch01ContourInputI00.row10.drop 304).take 16)=true ∧
 ((RHBatch01ContourInputR00.row10.drop 304).take 16).length=16 := by decide +kernel
theorem checked10_20 : check v 5440
 ((RHBatch01ContourInputR00.row10.drop 320).take 16) ((RHBatch01ContourInputI00.row10.drop 320).take 16)=true ∧
 ((RHBatch01ContourInputR00.row10.drop 320).take 16).length=16 := by decide +kernel
theorem checked10_21 : check v 5456
 ((RHBatch01ContourInputR00.row10.drop 336).take 16) ((RHBatch01ContourInputI00.row10.drop 336).take 16)=true ∧
 ((RHBatch01ContourInputR00.row10.drop 336).take 16).length=16 := by decide +kernel
theorem checked10_22 : check v 5472
 ((RHBatch01ContourInputR00.row10.drop 352).take 16) ((RHBatch01ContourInputI00.row10.drop 352).take 16)=true ∧
 ((RHBatch01ContourInputR00.row10.drop 352).take 16).length=16 := by decide +kernel
theorem checked10_23 : check v 5488
 ((RHBatch01ContourInputR00.row10.drop 368).take 16) ((RHBatch01ContourInputI00.row10.drop 368).take 16)=true ∧
 ((RHBatch01ContourInputR00.row10.drop 368).take 16).length=16 := by decide +kernel
theorem checked10_24 : check v 5504
 ((RHBatch01ContourInputR00.row10.drop 384).take 16) ((RHBatch01ContourInputI00.row10.drop 384).take 16)=true ∧
 ((RHBatch01ContourInputR00.row10.drop 384).take 16).length=16 := by decide +kernel
theorem checked10_25 : check v 5520
 ((RHBatch01ContourInputR00.row10.drop 400).take 16) ((RHBatch01ContourInputI00.row10.drop 400).take 16)=true ∧
 ((RHBatch01ContourInputR00.row10.drop 400).take 16).length=16 := by decide +kernel
theorem checked10_26 : check v 5536
 ((RHBatch01ContourInputR00.row10.drop 416).take 16) ((RHBatch01ContourInputI00.row10.drop 416).take 16)=true ∧
 ((RHBatch01ContourInputR00.row10.drop 416).take 16).length=16 := by decide +kernel
theorem checked10_27 : check v 5552
 ((RHBatch01ContourInputR00.row10.drop 432).take 16) ((RHBatch01ContourInputI00.row10.drop 432).take 16)=true ∧
 ((RHBatch01ContourInputR00.row10.drop 432).take 16).length=16 := by decide +kernel
theorem checked10_28 : check v 5568
 ((RHBatch01ContourInputR00.row10.drop 448).take 16) ((RHBatch01ContourInputI00.row10.drop 448).take 16)=true ∧
 ((RHBatch01ContourInputR00.row10.drop 448).take 16).length=16 := by decide +kernel
theorem checked10_29 : check v 5584
 ((RHBatch01ContourInputR00.row10.drop 464).take 16) ((RHBatch01ContourInputI00.row10.drop 464).take 16)=true ∧
 ((RHBatch01ContourInputR00.row10.drop 464).take 16).length=16 := by decide +kernel
theorem checked10_30 : check v 5600
 ((RHBatch01ContourInputR00.row10.drop 480).take 16) ((RHBatch01ContourInputI00.row10.drop 480).take 16)=true ∧
 ((RHBatch01ContourInputR00.row10.drop 480).take 16).length=16 := by decide +kernel
theorem checked10_31 : check v 5616
 ((RHBatch01ContourInputR00.row10.drop 496).take 16) ((RHBatch01ContourInputI00.row10.drop 496).take 16)=true ∧
 ((RHBatch01ContourInputR00.row10.drop 496).take 16).length=16 := by decide +kernel
theorem checked11_00 : check v 5632
 ((RHBatch01ContourInputR00.row11.drop 0).take 16) ((RHBatch01ContourInputI00.row11.drop 0).take 16)=true ∧
 ((RHBatch01ContourInputR00.row11.drop 0).take 16).length=16 := by decide +kernel
theorem checked11_01 : check v 5648
 ((RHBatch01ContourInputR00.row11.drop 16).take 16) ((RHBatch01ContourInputI00.row11.drop 16).take 16)=true ∧
 ((RHBatch01ContourInputR00.row11.drop 16).take 16).length=16 := by decide +kernel
theorem checked11_02 : check v 5664
 ((RHBatch01ContourInputR00.row11.drop 32).take 16) ((RHBatch01ContourInputI00.row11.drop 32).take 16)=true ∧
 ((RHBatch01ContourInputR00.row11.drop 32).take 16).length=16 := by decide +kernel
theorem checked11_03 : check v 5680
 ((RHBatch01ContourInputR00.row11.drop 48).take 16) ((RHBatch01ContourInputI00.row11.drop 48).take 16)=true ∧
 ((RHBatch01ContourInputR00.row11.drop 48).take 16).length=16 := by decide +kernel
theorem checked11_04 : check v 5696
 ((RHBatch01ContourInputR00.row11.drop 64).take 16) ((RHBatch01ContourInputI00.row11.drop 64).take 16)=true ∧
 ((RHBatch01ContourInputR00.row11.drop 64).take 16).length=16 := by decide +kernel
theorem checked11_05 : check v 5712
 ((RHBatch01ContourInputR00.row11.drop 80).take 16) ((RHBatch01ContourInputI00.row11.drop 80).take 16)=true ∧
 ((RHBatch01ContourInputR00.row11.drop 80).take 16).length=16 := by decide +kernel
theorem checked11_06 : check v 5728
 ((RHBatch01ContourInputR00.row11.drop 96).take 16) ((RHBatch01ContourInputI00.row11.drop 96).take 16)=true ∧
 ((RHBatch01ContourInputR00.row11.drop 96).take 16).length=16 := by decide +kernel
theorem checked11_07 : check v 5744
 ((RHBatch01ContourInputR00.row11.drop 112).take 16) ((RHBatch01ContourInputI00.row11.drop 112).take 16)=true ∧
 ((RHBatch01ContourInputR00.row11.drop 112).take 16).length=16 := by decide +kernel
theorem checked11_08 : check v 5760
 ((RHBatch01ContourInputR00.row11.drop 128).take 16) ((RHBatch01ContourInputI00.row11.drop 128).take 16)=true ∧
 ((RHBatch01ContourInputR00.row11.drop 128).take 16).length=16 := by decide +kernel
theorem checked11_09 : check v 5776
 ((RHBatch01ContourInputR00.row11.drop 144).take 16) ((RHBatch01ContourInputI00.row11.drop 144).take 16)=true ∧
 ((RHBatch01ContourInputR00.row11.drop 144).take 16).length=16 := by decide +kernel
theorem checked11_10 : check v 5792
 ((RHBatch01ContourInputR00.row11.drop 160).take 16) ((RHBatch01ContourInputI00.row11.drop 160).take 16)=true ∧
 ((RHBatch01ContourInputR00.row11.drop 160).take 16).length=16 := by decide +kernel
theorem checked11_11 : check v 5808
 ((RHBatch01ContourInputR00.row11.drop 176).take 16) ((RHBatch01ContourInputI00.row11.drop 176).take 16)=true ∧
 ((RHBatch01ContourInputR00.row11.drop 176).take 16).length=16 := by decide +kernel
theorem checked11_12 : check v 5824
 ((RHBatch01ContourInputR00.row11.drop 192).take 16) ((RHBatch01ContourInputI00.row11.drop 192).take 16)=true ∧
 ((RHBatch01ContourInputR00.row11.drop 192).take 16).length=16 := by decide +kernel
theorem checked11_13 : check v 5840
 ((RHBatch01ContourInputR00.row11.drop 208).take 16) ((RHBatch01ContourInputI00.row11.drop 208).take 16)=true ∧
 ((RHBatch01ContourInputR00.row11.drop 208).take 16).length=16 := by decide +kernel
theorem checked11_14 : check v 5856
 ((RHBatch01ContourInputR00.row11.drop 224).take 16) ((RHBatch01ContourInputI00.row11.drop 224).take 16)=true ∧
 ((RHBatch01ContourInputR00.row11.drop 224).take 16).length=16 := by decide +kernel
theorem checked11_15 : check v 5872
 ((RHBatch01ContourInputR00.row11.drop 240).take 16) ((RHBatch01ContourInputI00.row11.drop 240).take 16)=true ∧
 ((RHBatch01ContourInputR00.row11.drop 240).take 16).length=16 := by decide +kernel
theorem checked11_16 : check v 5888
 ((RHBatch01ContourInputR00.row11.drop 256).take 16) ((RHBatch01ContourInputI00.row11.drop 256).take 16)=true ∧
 ((RHBatch01ContourInputR00.row11.drop 256).take 16).length=16 := by decide +kernel
theorem checked11_17 : check v 5904
 ((RHBatch01ContourInputR00.row11.drop 272).take 16) ((RHBatch01ContourInputI00.row11.drop 272).take 16)=true ∧
 ((RHBatch01ContourInputR00.row11.drop 272).take 16).length=16 := by decide +kernel
theorem checked11_18 : check v 5920
 ((RHBatch01ContourInputR00.row11.drop 288).take 16) ((RHBatch01ContourInputI00.row11.drop 288).take 16)=true ∧
 ((RHBatch01ContourInputR00.row11.drop 288).take 16).length=16 := by decide +kernel
theorem checked11_19 : check v 5936
 ((RHBatch01ContourInputR00.row11.drop 304).take 16) ((RHBatch01ContourInputI00.row11.drop 304).take 16)=true ∧
 ((RHBatch01ContourInputR00.row11.drop 304).take 16).length=16 := by decide +kernel
theorem checked11_20 : check v 5952
 ((RHBatch01ContourInputR00.row11.drop 320).take 16) ((RHBatch01ContourInputI00.row11.drop 320).take 16)=true ∧
 ((RHBatch01ContourInputR00.row11.drop 320).take 16).length=16 := by decide +kernel
theorem checked11_21 : check v 5968
 ((RHBatch01ContourInputR00.row11.drop 336).take 16) ((RHBatch01ContourInputI00.row11.drop 336).take 16)=true ∧
 ((RHBatch01ContourInputR00.row11.drop 336).take 16).length=16 := by decide +kernel
theorem checked11_22 : check v 5984
 ((RHBatch01ContourInputR00.row11.drop 352).take 16) ((RHBatch01ContourInputI00.row11.drop 352).take 16)=true ∧
 ((RHBatch01ContourInputR00.row11.drop 352).take 16).length=16 := by decide +kernel
theorem checked11_23 : check v 6000
 ((RHBatch01ContourInputR00.row11.drop 368).take 16) ((RHBatch01ContourInputI00.row11.drop 368).take 16)=true ∧
 ((RHBatch01ContourInputR00.row11.drop 368).take 16).length=16 := by decide +kernel
theorem checked11_24 : check v 6016
 ((RHBatch01ContourInputR00.row11.drop 384).take 16) ((RHBatch01ContourInputI00.row11.drop 384).take 16)=true ∧
 ((RHBatch01ContourInputR00.row11.drop 384).take 16).length=16 := by decide +kernel
theorem checked11_25 : check v 6032
 ((RHBatch01ContourInputR00.row11.drop 400).take 16) ((RHBatch01ContourInputI00.row11.drop 400).take 16)=true ∧
 ((RHBatch01ContourInputR00.row11.drop 400).take 16).length=16 := by decide +kernel
theorem checked11_26 : check v 6048
 ((RHBatch01ContourInputR00.row11.drop 416).take 16) ((RHBatch01ContourInputI00.row11.drop 416).take 16)=true ∧
 ((RHBatch01ContourInputR00.row11.drop 416).take 16).length=16 := by decide +kernel
theorem checked11_27 : check v 6064
 ((RHBatch01ContourInputR00.row11.drop 432).take 16) ((RHBatch01ContourInputI00.row11.drop 432).take 16)=true ∧
 ((RHBatch01ContourInputR00.row11.drop 432).take 16).length=16 := by decide +kernel
theorem checked11_28 : check v 6080
 ((RHBatch01ContourInputR00.row11.drop 448).take 16) ((RHBatch01ContourInputI00.row11.drop 448).take 16)=true ∧
 ((RHBatch01ContourInputR00.row11.drop 448).take 16).length=16 := by decide +kernel
theorem checked11_29 : check v 6096
 ((RHBatch01ContourInputR00.row11.drop 464).take 16) ((RHBatch01ContourInputI00.row11.drop 464).take 16)=true ∧
 ((RHBatch01ContourInputR00.row11.drop 464).take 16).length=16 := by decide +kernel
theorem checked11_30 : check v 6112
 ((RHBatch01ContourInputR00.row11.drop 480).take 16) ((RHBatch01ContourInputI00.row11.drop 480).take 16)=true ∧
 ((RHBatch01ContourInputR00.row11.drop 480).take 16).length=16 := by decide +kernel
theorem checked11_31 : check v 6128
 ((RHBatch01ContourInputR00.row11.drop 496).take 16) ((RHBatch01ContourInputI00.row11.drop 496).take 16)=true ∧
 ((RHBatch01ContourInputR00.row11.drop 496).take 16).length=16 := by decide +kernel
theorem checked12_00 : check v 6144
 ((RHBatch01ContourInputR00.row12.drop 0).take 16) ((RHBatch01ContourInputI00.row12.drop 0).take 16)=true ∧
 ((RHBatch01ContourInputR00.row12.drop 0).take 16).length=16 := by decide +kernel
theorem checked12_01 : check v 6160
 ((RHBatch01ContourInputR00.row12.drop 16).take 16) ((RHBatch01ContourInputI00.row12.drop 16).take 16)=true ∧
 ((RHBatch01ContourInputR00.row12.drop 16).take 16).length=16 := by decide +kernel
theorem checked12_02 : check v 6176
 ((RHBatch01ContourInputR00.row12.drop 32).take 16) ((RHBatch01ContourInputI00.row12.drop 32).take 16)=true ∧
 ((RHBatch01ContourInputR00.row12.drop 32).take 16).length=16 := by decide +kernel
theorem checked12_03 : check v 6192
 ((RHBatch01ContourInputR00.row12.drop 48).take 16) ((RHBatch01ContourInputI00.row12.drop 48).take 16)=true ∧
 ((RHBatch01ContourInputR00.row12.drop 48).take 16).length=16 := by decide +kernel
theorem checked12_04 : check v 6208
 ((RHBatch01ContourInputR00.row12.drop 64).take 16) ((RHBatch01ContourInputI00.row12.drop 64).take 16)=true ∧
 ((RHBatch01ContourInputR00.row12.drop 64).take 16).length=16 := by decide +kernel
theorem checked12_05 : check v 6224
 ((RHBatch01ContourInputR00.row12.drop 80).take 16) ((RHBatch01ContourInputI00.row12.drop 80).take 16)=true ∧
 ((RHBatch01ContourInputR00.row12.drop 80).take 16).length=16 := by decide +kernel
theorem checked12_06 : check v 6240
 ((RHBatch01ContourInputR00.row12.drop 96).take 16) ((RHBatch01ContourInputI00.row12.drop 96).take 16)=true ∧
 ((RHBatch01ContourInputR00.row12.drop 96).take 16).length=16 := by decide +kernel
theorem checked12_07 : check v 6256
 ((RHBatch01ContourInputR00.row12.drop 112).take 16) ((RHBatch01ContourInputI00.row12.drop 112).take 16)=true ∧
 ((RHBatch01ContourInputR00.row12.drop 112).take 16).length=16 := by decide +kernel
theorem checked12_08 : check v 6272
 ((RHBatch01ContourInputR00.row12.drop 128).take 16) ((RHBatch01ContourInputI00.row12.drop 128).take 16)=true ∧
 ((RHBatch01ContourInputR00.row12.drop 128).take 16).length=16 := by decide +kernel
theorem checked12_09 : check v 6288
 ((RHBatch01ContourInputR00.row12.drop 144).take 16) ((RHBatch01ContourInputI00.row12.drop 144).take 16)=true ∧
 ((RHBatch01ContourInputR00.row12.drop 144).take 16).length=16 := by decide +kernel
theorem checked12_10 : check v 6304
 ((RHBatch01ContourInputR00.row12.drop 160).take 16) ((RHBatch01ContourInputI00.row12.drop 160).take 16)=true ∧
 ((RHBatch01ContourInputR00.row12.drop 160).take 16).length=16 := by decide +kernel
theorem checked12_11 : check v 6320
 ((RHBatch01ContourInputR00.row12.drop 176).take 16) ((RHBatch01ContourInputI00.row12.drop 176).take 16)=true ∧
 ((RHBatch01ContourInputR00.row12.drop 176).take 16).length=16 := by decide +kernel
theorem checked12_12 : check v 6336
 ((RHBatch01ContourInputR00.row12.drop 192).take 16) ((RHBatch01ContourInputI00.row12.drop 192).take 16)=true ∧
 ((RHBatch01ContourInputR00.row12.drop 192).take 16).length=16 := by decide +kernel
theorem checked12_13 : check v 6352
 ((RHBatch01ContourInputR00.row12.drop 208).take 16) ((RHBatch01ContourInputI00.row12.drop 208).take 16)=true ∧
 ((RHBatch01ContourInputR00.row12.drop 208).take 16).length=16 := by decide +kernel
theorem checked12_14 : check v 6368
 ((RHBatch01ContourInputR00.row12.drop 224).take 16) ((RHBatch01ContourInputI00.row12.drop 224).take 16)=true ∧
 ((RHBatch01ContourInputR00.row12.drop 224).take 16).length=16 := by decide +kernel
theorem checked12_15 : check v 6384
 ((RHBatch01ContourInputR00.row12.drop 240).take 16) ((RHBatch01ContourInputI00.row12.drop 240).take 16)=true ∧
 ((RHBatch01ContourInputR00.row12.drop 240).take 16).length=16 := by decide +kernel
theorem checked12_16 : check v 6400
 ((RHBatch01ContourInputR00.row12.drop 256).take 16) ((RHBatch01ContourInputI00.row12.drop 256).take 16)=true ∧
 ((RHBatch01ContourInputR00.row12.drop 256).take 16).length=16 := by decide +kernel
theorem checked12_17 : check v 6416
 ((RHBatch01ContourInputR00.row12.drop 272).take 16) ((RHBatch01ContourInputI00.row12.drop 272).take 16)=true ∧
 ((RHBatch01ContourInputR00.row12.drop 272).take 16).length=16 := by decide +kernel
theorem checked12_18 : check v 6432
 ((RHBatch01ContourInputR00.row12.drop 288).take 16) ((RHBatch01ContourInputI00.row12.drop 288).take 16)=true ∧
 ((RHBatch01ContourInputR00.row12.drop 288).take 16).length=16 := by decide +kernel
theorem checked12_19 : check v 6448
 ((RHBatch01ContourInputR00.row12.drop 304).take 16) ((RHBatch01ContourInputI00.row12.drop 304).take 16)=true ∧
 ((RHBatch01ContourInputR00.row12.drop 304).take 16).length=16 := by decide +kernel
theorem checked12_20 : check v 6464
 ((RHBatch01ContourInputR00.row12.drop 320).take 16) ((RHBatch01ContourInputI00.row12.drop 320).take 16)=true ∧
 ((RHBatch01ContourInputR00.row12.drop 320).take 16).length=16 := by decide +kernel
theorem checked12_21 : check v 6480
 ((RHBatch01ContourInputR00.row12.drop 336).take 16) ((RHBatch01ContourInputI00.row12.drop 336).take 16)=true ∧
 ((RHBatch01ContourInputR00.row12.drop 336).take 16).length=16 := by decide +kernel
theorem checked12_22 : check v 6496
 ((RHBatch01ContourInputR00.row12.drop 352).take 16) ((RHBatch01ContourInputI00.row12.drop 352).take 16)=true ∧
 ((RHBatch01ContourInputR00.row12.drop 352).take 16).length=16 := by decide +kernel
theorem checked12_23 : check v 6512
 ((RHBatch01ContourInputR00.row12.drop 368).take 16) ((RHBatch01ContourInputI00.row12.drop 368).take 16)=true ∧
 ((RHBatch01ContourInputR00.row12.drop 368).take 16).length=16 := by decide +kernel
theorem checked12_24 : check v 6528
 ((RHBatch01ContourInputR00.row12.drop 384).take 16) ((RHBatch01ContourInputI00.row12.drop 384).take 16)=true ∧
 ((RHBatch01ContourInputR00.row12.drop 384).take 16).length=16 := by decide +kernel
theorem checked12_25 : check v 6544
 ((RHBatch01ContourInputR00.row12.drop 400).take 16) ((RHBatch01ContourInputI00.row12.drop 400).take 16)=true ∧
 ((RHBatch01ContourInputR00.row12.drop 400).take 16).length=16 := by decide +kernel
theorem checked12_26 : check v 6560
 ((RHBatch01ContourInputR00.row12.drop 416).take 16) ((RHBatch01ContourInputI00.row12.drop 416).take 16)=true ∧
 ((RHBatch01ContourInputR00.row12.drop 416).take 16).length=16 := by decide +kernel
theorem checked12_27 : check v 6576
 ((RHBatch01ContourInputR00.row12.drop 432).take 16) ((RHBatch01ContourInputI00.row12.drop 432).take 16)=true ∧
 ((RHBatch01ContourInputR00.row12.drop 432).take 16).length=16 := by decide +kernel
theorem checked12_28 : check v 6592
 ((RHBatch01ContourInputR00.row12.drop 448).take 16) ((RHBatch01ContourInputI00.row12.drop 448).take 16)=true ∧
 ((RHBatch01ContourInputR00.row12.drop 448).take 16).length=16 := by decide +kernel
theorem checked12_29 : check v 6608
 ((RHBatch01ContourInputR00.row12.drop 464).take 16) ((RHBatch01ContourInputI00.row12.drop 464).take 16)=true ∧
 ((RHBatch01ContourInputR00.row12.drop 464).take 16).length=16 := by decide +kernel
theorem checked12_30 : check v 6624
 ((RHBatch01ContourInputR00.row12.drop 480).take 16) ((RHBatch01ContourInputI00.row12.drop 480).take 16)=true ∧
 ((RHBatch01ContourInputR00.row12.drop 480).take 16).length=16 := by decide +kernel
theorem checked12_31 : check v 6640
 ((RHBatch01ContourInputR00.row12.drop 496).take 16) ((RHBatch01ContourInputI00.row12.drop 496).take 16)=true ∧
 ((RHBatch01ContourInputR00.row12.drop 496).take 16).length=16 := by decide +kernel
theorem checked13_00 : check v 6656
 ((RHBatch01ContourInputR00.row13.drop 0).take 16) ((RHBatch01ContourInputI00.row13.drop 0).take 16)=true ∧
 ((RHBatch01ContourInputR00.row13.drop 0).take 16).length=16 := by decide +kernel
theorem checked13_01 : check v 6672
 ((RHBatch01ContourInputR00.row13.drop 16).take 16) ((RHBatch01ContourInputI00.row13.drop 16).take 16)=true ∧
 ((RHBatch01ContourInputR00.row13.drop 16).take 16).length=16 := by decide +kernel
theorem checked13_02 : check v 6688
 ((RHBatch01ContourInputR00.row13.drop 32).take 16) ((RHBatch01ContourInputI00.row13.drop 32).take 16)=true ∧
 ((RHBatch01ContourInputR00.row13.drop 32).take 16).length=16 := by decide +kernel
theorem checked13_03 : check v 6704
 ((RHBatch01ContourInputR00.row13.drop 48).take 16) ((RHBatch01ContourInputI00.row13.drop 48).take 16)=true ∧
 ((RHBatch01ContourInputR00.row13.drop 48).take 16).length=16 := by decide +kernel
theorem checked13_04 : check v 6720
 ((RHBatch01ContourInputR00.row13.drop 64).take 16) ((RHBatch01ContourInputI00.row13.drop 64).take 16)=true ∧
 ((RHBatch01ContourInputR00.row13.drop 64).take 16).length=16 := by decide +kernel
theorem checked13_05 : check v 6736
 ((RHBatch01ContourInputR00.row13.drop 80).take 16) ((RHBatch01ContourInputI00.row13.drop 80).take 16)=true ∧
 ((RHBatch01ContourInputR00.row13.drop 80).take 16).length=16 := by decide +kernel
theorem checked13_06 : check v 6752
 ((RHBatch01ContourInputR00.row13.drop 96).take 16) ((RHBatch01ContourInputI00.row13.drop 96).take 16)=true ∧
 ((RHBatch01ContourInputR00.row13.drop 96).take 16).length=16 := by decide +kernel
theorem checked13_07 : check v 6768
 ((RHBatch01ContourInputR00.row13.drop 112).take 16) ((RHBatch01ContourInputI00.row13.drop 112).take 16)=true ∧
 ((RHBatch01ContourInputR00.row13.drop 112).take 16).length=16 := by decide +kernel
theorem checked13_08 : check v 6784
 ((RHBatch01ContourInputR00.row13.drop 128).take 16) ((RHBatch01ContourInputI00.row13.drop 128).take 16)=true ∧
 ((RHBatch01ContourInputR00.row13.drop 128).take 16).length=16 := by decide +kernel
theorem checked13_09 : check v 6800
 ((RHBatch01ContourInputR00.row13.drop 144).take 16) ((RHBatch01ContourInputI00.row13.drop 144).take 16)=true ∧
 ((RHBatch01ContourInputR00.row13.drop 144).take 16).length=16 := by decide +kernel
theorem checked13_10 : check v 6816
 ((RHBatch01ContourInputR00.row13.drop 160).take 16) ((RHBatch01ContourInputI00.row13.drop 160).take 16)=true ∧
 ((RHBatch01ContourInputR00.row13.drop 160).take 16).length=16 := by decide +kernel
theorem checked13_11 : check v 6832
 ((RHBatch01ContourInputR00.row13.drop 176).take 16) ((RHBatch01ContourInputI00.row13.drop 176).take 16)=true ∧
 ((RHBatch01ContourInputR00.row13.drop 176).take 16).length=16 := by decide +kernel
theorem checked13_12 : check v 6848
 ((RHBatch01ContourInputR00.row13.drop 192).take 16) ((RHBatch01ContourInputI00.row13.drop 192).take 16)=true ∧
 ((RHBatch01ContourInputR00.row13.drop 192).take 16).length=16 := by decide +kernel
theorem checked13_13 : check v 6864
 ((RHBatch01ContourInputR00.row13.drop 208).take 16) ((RHBatch01ContourInputI00.row13.drop 208).take 16)=true ∧
 ((RHBatch01ContourInputR00.row13.drop 208).take 16).length=16 := by decide +kernel
theorem checked13_14 : check v 6880
 ((RHBatch01ContourInputR00.row13.drop 224).take 16) ((RHBatch01ContourInputI00.row13.drop 224).take 16)=true ∧
 ((RHBatch01ContourInputR00.row13.drop 224).take 16).length=16 := by decide +kernel
theorem checked13_15 : check v 6896
 ((RHBatch01ContourInputR00.row13.drop 240).take 16) ((RHBatch01ContourInputI00.row13.drop 240).take 16)=true ∧
 ((RHBatch01ContourInputR00.row13.drop 240).take 16).length=16 := by decide +kernel
theorem checked13_16 : check v 6912
 ((RHBatch01ContourInputR00.row13.drop 256).take 16) ((RHBatch01ContourInputI00.row13.drop 256).take 16)=true ∧
 ((RHBatch01ContourInputR00.row13.drop 256).take 16).length=16 := by decide +kernel
theorem checked13_17 : check v 6928
 ((RHBatch01ContourInputR00.row13.drop 272).take 16) ((RHBatch01ContourInputI00.row13.drop 272).take 16)=true ∧
 ((RHBatch01ContourInputR00.row13.drop 272).take 16).length=16 := by decide +kernel
theorem checked13_18 : check v 6944
 ((RHBatch01ContourInputR00.row13.drop 288).take 16) ((RHBatch01ContourInputI00.row13.drop 288).take 16)=true ∧
 ((RHBatch01ContourInputR00.row13.drop 288).take 16).length=16 := by decide +kernel
theorem checked13_19 : check v 6960
 ((RHBatch01ContourInputR00.row13.drop 304).take 16) ((RHBatch01ContourInputI00.row13.drop 304).take 16)=true ∧
 ((RHBatch01ContourInputR00.row13.drop 304).take 16).length=16 := by decide +kernel
theorem checked13_20 : check v 6976
 ((RHBatch01ContourInputR00.row13.drop 320).take 16) ((RHBatch01ContourInputI00.row13.drop 320).take 16)=true ∧
 ((RHBatch01ContourInputR00.row13.drop 320).take 16).length=16 := by decide +kernel
theorem checked13_21 : check v 6992
 ((RHBatch01ContourInputR00.row13.drop 336).take 16) ((RHBatch01ContourInputI00.row13.drop 336).take 16)=true ∧
 ((RHBatch01ContourInputR00.row13.drop 336).take 16).length=16 := by decide +kernel
theorem checked13_22 : check v 7008
 ((RHBatch01ContourInputR00.row13.drop 352).take 16) ((RHBatch01ContourInputI00.row13.drop 352).take 16)=true ∧
 ((RHBatch01ContourInputR00.row13.drop 352).take 16).length=16 := by decide +kernel
theorem checked13_23 : check v 7024
 ((RHBatch01ContourInputR00.row13.drop 368).take 16) ((RHBatch01ContourInputI00.row13.drop 368).take 16)=true ∧
 ((RHBatch01ContourInputR00.row13.drop 368).take 16).length=16 := by decide +kernel
theorem checked13_24 : check v 7040
 ((RHBatch01ContourInputR00.row13.drop 384).take 16) ((RHBatch01ContourInputI00.row13.drop 384).take 16)=true ∧
 ((RHBatch01ContourInputR00.row13.drop 384).take 16).length=16 := by decide +kernel
theorem checked13_25 : check v 7056
 ((RHBatch01ContourInputR00.row13.drop 400).take 16) ((RHBatch01ContourInputI00.row13.drop 400).take 16)=true ∧
 ((RHBatch01ContourInputR00.row13.drop 400).take 16).length=16 := by decide +kernel
theorem checked13_26 : check v 7072
 ((RHBatch01ContourInputR00.row13.drop 416).take 16) ((RHBatch01ContourInputI00.row13.drop 416).take 16)=true ∧
 ((RHBatch01ContourInputR00.row13.drop 416).take 16).length=16 := by decide +kernel
theorem checked13_27 : check v 7088
 ((RHBatch01ContourInputR00.row13.drop 432).take 16) ((RHBatch01ContourInputI00.row13.drop 432).take 16)=true ∧
 ((RHBatch01ContourInputR00.row13.drop 432).take 16).length=16 := by decide +kernel
theorem checked13_28 : check v 7104
 ((RHBatch01ContourInputR00.row13.drop 448).take 16) ((RHBatch01ContourInputI00.row13.drop 448).take 16)=true ∧
 ((RHBatch01ContourInputR00.row13.drop 448).take 16).length=16 := by decide +kernel
theorem checked13_29 : check v 7120
 ((RHBatch01ContourInputR00.row13.drop 464).take 16) ((RHBatch01ContourInputI00.row13.drop 464).take 16)=true ∧
 ((RHBatch01ContourInputR00.row13.drop 464).take 16).length=16 := by decide +kernel
theorem checked13_30 : check v 7136
 ((RHBatch01ContourInputR00.row13.drop 480).take 16) ((RHBatch01ContourInputI00.row13.drop 480).take 16)=true ∧
 ((RHBatch01ContourInputR00.row13.drop 480).take 16).length=16 := by decide +kernel
theorem checked13_31 : check v 7152
 ((RHBatch01ContourInputR00.row13.drop 496).take 16) ((RHBatch01ContourInputI00.row13.drop 496).take 16)=true ∧
 ((RHBatch01ContourInputR00.row13.drop 496).take 16).length=16 := by decide +kernel
theorem checked14_00 : check v 7168
 ((RHBatch01ContourInputR00.row14.drop 0).take 16) ((RHBatch01ContourInputI00.row14.drop 0).take 16)=true ∧
 ((RHBatch01ContourInputR00.row14.drop 0).take 16).length=16 := by decide +kernel
theorem checked14_01 : check v 7184
 ((RHBatch01ContourInputR00.row14.drop 16).take 16) ((RHBatch01ContourInputI00.row14.drop 16).take 16)=true ∧
 ((RHBatch01ContourInputR00.row14.drop 16).take 16).length=16 := by decide +kernel
theorem checked14_02 : check v 7200
 ((RHBatch01ContourInputR00.row14.drop 32).take 16) ((RHBatch01ContourInputI00.row14.drop 32).take 16)=true ∧
 ((RHBatch01ContourInputR00.row14.drop 32).take 16).length=16 := by decide +kernel
theorem checked14_03 : check v 7216
 ((RHBatch01ContourInputR00.row14.drop 48).take 16) ((RHBatch01ContourInputI00.row14.drop 48).take 16)=true ∧
 ((RHBatch01ContourInputR00.row14.drop 48).take 16).length=16 := by decide +kernel
theorem checked14_04 : check v 7232
 ((RHBatch01ContourInputR00.row14.drop 64).take 16) ((RHBatch01ContourInputI00.row14.drop 64).take 16)=true ∧
 ((RHBatch01ContourInputR00.row14.drop 64).take 16).length=16 := by decide +kernel
theorem checked14_05 : check v 7248
 ((RHBatch01ContourInputR00.row14.drop 80).take 16) ((RHBatch01ContourInputI00.row14.drop 80).take 16)=true ∧
 ((RHBatch01ContourInputR00.row14.drop 80).take 16).length=16 := by decide +kernel
theorem checked14_06 : check v 7264
 ((RHBatch01ContourInputR00.row14.drop 96).take 16) ((RHBatch01ContourInputI00.row14.drop 96).take 16)=true ∧
 ((RHBatch01ContourInputR00.row14.drop 96).take 16).length=16 := by decide +kernel
theorem checked14_07 : check v 7280
 ((RHBatch01ContourInputR00.row14.drop 112).take 16) ((RHBatch01ContourInputI00.row14.drop 112).take 16)=true ∧
 ((RHBatch01ContourInputR00.row14.drop 112).take 16).length=16 := by decide +kernel
theorem checked14_08 : check v 7296
 ((RHBatch01ContourInputR00.row14.drop 128).take 16) ((RHBatch01ContourInputI00.row14.drop 128).take 16)=true ∧
 ((RHBatch01ContourInputR00.row14.drop 128).take 16).length=16 := by decide +kernel
theorem checked14_09 : check v 7312
 ((RHBatch01ContourInputR00.row14.drop 144).take 16) ((RHBatch01ContourInputI00.row14.drop 144).take 16)=true ∧
 ((RHBatch01ContourInputR00.row14.drop 144).take 16).length=16 := by decide +kernel
theorem checked14_10 : check v 7328
 ((RHBatch01ContourInputR00.row14.drop 160).take 16) ((RHBatch01ContourInputI00.row14.drop 160).take 16)=true ∧
 ((RHBatch01ContourInputR00.row14.drop 160).take 16).length=16 := by decide +kernel
theorem checked14_11 : check v 7344
 ((RHBatch01ContourInputR00.row14.drop 176).take 16) ((RHBatch01ContourInputI00.row14.drop 176).take 16)=true ∧
 ((RHBatch01ContourInputR00.row14.drop 176).take 16).length=16 := by decide +kernel
theorem checked14_12 : check v 7360
 ((RHBatch01ContourInputR00.row14.drop 192).take 16) ((RHBatch01ContourInputI00.row14.drop 192).take 16)=true ∧
 ((RHBatch01ContourInputR00.row14.drop 192).take 16).length=16 := by decide +kernel
theorem checked14_13 : check v 7376
 ((RHBatch01ContourInputR00.row14.drop 208).take 16) ((RHBatch01ContourInputI00.row14.drop 208).take 16)=true ∧
 ((RHBatch01ContourInputR00.row14.drop 208).take 16).length=16 := by decide +kernel
theorem checked14_14 : check v 7392
 ((RHBatch01ContourInputR00.row14.drop 224).take 16) ((RHBatch01ContourInputI00.row14.drop 224).take 16)=true ∧
 ((RHBatch01ContourInputR00.row14.drop 224).take 16).length=16 := by decide +kernel
theorem checked14_15 : check v 7408
 ((RHBatch01ContourInputR00.row14.drop 240).take 16) ((RHBatch01ContourInputI00.row14.drop 240).take 16)=true ∧
 ((RHBatch01ContourInputR00.row14.drop 240).take 16).length=16 := by decide +kernel
theorem checked14_16 : check v 7424
 ((RHBatch01ContourInputR00.row14.drop 256).take 16) ((RHBatch01ContourInputI00.row14.drop 256).take 16)=true ∧
 ((RHBatch01ContourInputR00.row14.drop 256).take 16).length=16 := by decide +kernel
theorem checked14_17 : check v 7440
 ((RHBatch01ContourInputR00.row14.drop 272).take 16) ((RHBatch01ContourInputI00.row14.drop 272).take 16)=true ∧
 ((RHBatch01ContourInputR00.row14.drop 272).take 16).length=16 := by decide +kernel
theorem checked14_18 : check v 7456
 ((RHBatch01ContourInputR00.row14.drop 288).take 16) ((RHBatch01ContourInputI00.row14.drop 288).take 16)=true ∧
 ((RHBatch01ContourInputR00.row14.drop 288).take 16).length=16 := by decide +kernel
theorem checked14_19 : check v 7472
 ((RHBatch01ContourInputR00.row14.drop 304).take 16) ((RHBatch01ContourInputI00.row14.drop 304).take 16)=true ∧
 ((RHBatch01ContourInputR00.row14.drop 304).take 16).length=16 := by decide +kernel
theorem checked14_20 : check v 7488
 ((RHBatch01ContourInputR00.row14.drop 320).take 16) ((RHBatch01ContourInputI00.row14.drop 320).take 16)=true ∧
 ((RHBatch01ContourInputR00.row14.drop 320).take 16).length=16 := by decide +kernel
theorem checked14_21 : check v 7504
 ((RHBatch01ContourInputR00.row14.drop 336).take 16) ((RHBatch01ContourInputI00.row14.drop 336).take 16)=true ∧
 ((RHBatch01ContourInputR00.row14.drop 336).take 16).length=16 := by decide +kernel
theorem checked14_22 : check v 7520
 ((RHBatch01ContourInputR00.row14.drop 352).take 16) ((RHBatch01ContourInputI00.row14.drop 352).take 16)=true ∧
 ((RHBatch01ContourInputR00.row14.drop 352).take 16).length=16 := by decide +kernel
theorem checked14_23 : check v 7536
 ((RHBatch01ContourInputR00.row14.drop 368).take 16) ((RHBatch01ContourInputI00.row14.drop 368).take 16)=true ∧
 ((RHBatch01ContourInputR00.row14.drop 368).take 16).length=16 := by decide +kernel
theorem checked14_24 : check v 7552
 ((RHBatch01ContourInputR00.row14.drop 384).take 16) ((RHBatch01ContourInputI00.row14.drop 384).take 16)=true ∧
 ((RHBatch01ContourInputR00.row14.drop 384).take 16).length=16 := by decide +kernel
theorem checked14_25 : check v 7568
 ((RHBatch01ContourInputR00.row14.drop 400).take 16) ((RHBatch01ContourInputI00.row14.drop 400).take 16)=true ∧
 ((RHBatch01ContourInputR00.row14.drop 400).take 16).length=16 := by decide +kernel
theorem checked14_26 : check v 7584
 ((RHBatch01ContourInputR00.row14.drop 416).take 16) ((RHBatch01ContourInputI00.row14.drop 416).take 16)=true ∧
 ((RHBatch01ContourInputR00.row14.drop 416).take 16).length=16 := by decide +kernel
theorem checked14_27 : check v 7600
 ((RHBatch01ContourInputR00.row14.drop 432).take 16) ((RHBatch01ContourInputI00.row14.drop 432).take 16)=true ∧
 ((RHBatch01ContourInputR00.row14.drop 432).take 16).length=16 := by decide +kernel
theorem checked14_28 : check v 7616
 ((RHBatch01ContourInputR00.row14.drop 448).take 16) ((RHBatch01ContourInputI00.row14.drop 448).take 16)=true ∧
 ((RHBatch01ContourInputR00.row14.drop 448).take 16).length=16 := by decide +kernel
theorem checked14_29 : check v 7632
 ((RHBatch01ContourInputR00.row14.drop 464).take 16) ((RHBatch01ContourInputI00.row14.drop 464).take 16)=true ∧
 ((RHBatch01ContourInputR00.row14.drop 464).take 16).length=16 := by decide +kernel
theorem checked14_30 : check v 7648
 ((RHBatch01ContourInputR00.row14.drop 480).take 16) ((RHBatch01ContourInputI00.row14.drop 480).take 16)=true ∧
 ((RHBatch01ContourInputR00.row14.drop 480).take 16).length=16 := by decide +kernel
theorem checked14_31 : check v 7664
 ((RHBatch01ContourInputR00.row14.drop 496).take 16) ((RHBatch01ContourInputI00.row14.drop 496).take 16)=true ∧
 ((RHBatch01ContourInputR00.row14.drop 496).take 16).length=16 := by decide +kernel
theorem checked15_00 : check v 7680
 ((RHBatch01ContourInputR00.row15.drop 0).take 16) ((RHBatch01ContourInputI00.row15.drop 0).take 16)=true ∧
 ((RHBatch01ContourInputR00.row15.drop 0).take 16).length=16 := by decide +kernel
theorem checked15_01 : check v 7696
 ((RHBatch01ContourInputR00.row15.drop 16).take 16) ((RHBatch01ContourInputI00.row15.drop 16).take 16)=true ∧
 ((RHBatch01ContourInputR00.row15.drop 16).take 16).length=16 := by decide +kernel
theorem checked15_02 : check v 7712
 ((RHBatch01ContourInputR00.row15.drop 32).take 16) ((RHBatch01ContourInputI00.row15.drop 32).take 16)=true ∧
 ((RHBatch01ContourInputR00.row15.drop 32).take 16).length=16 := by decide +kernel
theorem checked15_03 : check v 7728
 ((RHBatch01ContourInputR00.row15.drop 48).take 16) ((RHBatch01ContourInputI00.row15.drop 48).take 16)=true ∧
 ((RHBatch01ContourInputR00.row15.drop 48).take 16).length=16 := by decide +kernel
theorem checked15_04 : check v 7744
 ((RHBatch01ContourInputR00.row15.drop 64).take 16) ((RHBatch01ContourInputI00.row15.drop 64).take 16)=true ∧
 ((RHBatch01ContourInputR00.row15.drop 64).take 16).length=16 := by decide +kernel
theorem checked15_05 : check v 7760
 ((RHBatch01ContourInputR00.row15.drop 80).take 16) ((RHBatch01ContourInputI00.row15.drop 80).take 16)=true ∧
 ((RHBatch01ContourInputR00.row15.drop 80).take 16).length=16 := by decide +kernel
theorem checked15_06 : check v 7776
 ((RHBatch01ContourInputR00.row15.drop 96).take 16) ((RHBatch01ContourInputI00.row15.drop 96).take 16)=true ∧
 ((RHBatch01ContourInputR00.row15.drop 96).take 16).length=16 := by decide +kernel
theorem checked15_07 : check v 7792
 ((RHBatch01ContourInputR00.row15.drop 112).take 16) ((RHBatch01ContourInputI00.row15.drop 112).take 16)=true ∧
 ((RHBatch01ContourInputR00.row15.drop 112).take 16).length=16 := by decide +kernel
theorem checked15_08 : check v 7808
 ((RHBatch01ContourInputR00.row15.drop 128).take 16) ((RHBatch01ContourInputI00.row15.drop 128).take 16)=true ∧
 ((RHBatch01ContourInputR00.row15.drop 128).take 16).length=16 := by decide +kernel
theorem checked15_09 : check v 7824
 ((RHBatch01ContourInputR00.row15.drop 144).take 16) ((RHBatch01ContourInputI00.row15.drop 144).take 16)=true ∧
 ((RHBatch01ContourInputR00.row15.drop 144).take 16).length=16 := by decide +kernel
theorem checked15_10 : check v 7840
 ((RHBatch01ContourInputR00.row15.drop 160).take 16) ((RHBatch01ContourInputI00.row15.drop 160).take 16)=true ∧
 ((RHBatch01ContourInputR00.row15.drop 160).take 16).length=16 := by decide +kernel
theorem checked15_11 : check v 7856
 ((RHBatch01ContourInputR00.row15.drop 176).take 16) ((RHBatch01ContourInputI00.row15.drop 176).take 16)=true ∧
 ((RHBatch01ContourInputR00.row15.drop 176).take 16).length=16 := by decide +kernel
theorem checked15_12 : check v 7872
 ((RHBatch01ContourInputR00.row15.drop 192).take 16) ((RHBatch01ContourInputI00.row15.drop 192).take 16)=true ∧
 ((RHBatch01ContourInputR00.row15.drop 192).take 16).length=16 := by decide +kernel
theorem checked15_13 : check v 7888
 ((RHBatch01ContourInputR00.row15.drop 208).take 16) ((RHBatch01ContourInputI00.row15.drop 208).take 16)=true ∧
 ((RHBatch01ContourInputR00.row15.drop 208).take 16).length=16 := by decide +kernel
theorem checked15_14 : check v 7904
 ((RHBatch01ContourInputR00.row15.drop 224).take 16) ((RHBatch01ContourInputI00.row15.drop 224).take 16)=true ∧
 ((RHBatch01ContourInputR00.row15.drop 224).take 16).length=16 := by decide +kernel
theorem checked15_15 : check v 7920
 ((RHBatch01ContourInputR00.row15.drop 240).take 16) ((RHBatch01ContourInputI00.row15.drop 240).take 16)=true ∧
 ((RHBatch01ContourInputR00.row15.drop 240).take 16).length=16 := by decide +kernel
theorem checked15_16 : check v 7936
 ((RHBatch01ContourInputR00.row15.drop 256).take 16) ((RHBatch01ContourInputI00.row15.drop 256).take 16)=true ∧
 ((RHBatch01ContourInputR00.row15.drop 256).take 16).length=16 := by decide +kernel
theorem checked15_17 : check v 7952
 ((RHBatch01ContourInputR00.row15.drop 272).take 16) ((RHBatch01ContourInputI00.row15.drop 272).take 16)=true ∧
 ((RHBatch01ContourInputR00.row15.drop 272).take 16).length=16 := by decide +kernel
theorem checked15_18 : check v 7968
 ((RHBatch01ContourInputR00.row15.drop 288).take 16) ((RHBatch01ContourInputI00.row15.drop 288).take 16)=true ∧
 ((RHBatch01ContourInputR00.row15.drop 288).take 16).length=16 := by decide +kernel
theorem checked15_19 : check v 7984
 ((RHBatch01ContourInputR00.row15.drop 304).take 16) ((RHBatch01ContourInputI00.row15.drop 304).take 16)=true ∧
 ((RHBatch01ContourInputR00.row15.drop 304).take 16).length=16 := by decide +kernel
theorem checked15_20 : check v 8000
 ((RHBatch01ContourInputR00.row15.drop 320).take 16) ((RHBatch01ContourInputI00.row15.drop 320).take 16)=true ∧
 ((RHBatch01ContourInputR00.row15.drop 320).take 16).length=16 := by decide +kernel
theorem checked15_21 : check v 8016
 ((RHBatch01ContourInputR00.row15.drop 336).take 16) ((RHBatch01ContourInputI00.row15.drop 336).take 16)=true ∧
 ((RHBatch01ContourInputR00.row15.drop 336).take 16).length=16 := by decide +kernel
theorem checked15_22 : check v 8032
 ((RHBatch01ContourInputR00.row15.drop 352).take 16) ((RHBatch01ContourInputI00.row15.drop 352).take 16)=true ∧
 ((RHBatch01ContourInputR00.row15.drop 352).take 16).length=16 := by decide +kernel
theorem checked15_23 : check v 8048
 ((RHBatch01ContourInputR00.row15.drop 368).take 16) ((RHBatch01ContourInputI00.row15.drop 368).take 16)=true ∧
 ((RHBatch01ContourInputR00.row15.drop 368).take 16).length=16 := by decide +kernel
theorem checked15_24 : check v 8064
 ((RHBatch01ContourInputR00.row15.drop 384).take 16) ((RHBatch01ContourInputI00.row15.drop 384).take 16)=true ∧
 ((RHBatch01ContourInputR00.row15.drop 384).take 16).length=16 := by decide +kernel
theorem checked15_25 : check v 8080
 ((RHBatch01ContourInputR00.row15.drop 400).take 16) ((RHBatch01ContourInputI00.row15.drop 400).take 16)=true ∧
 ((RHBatch01ContourInputR00.row15.drop 400).take 16).length=16 := by decide +kernel
theorem checked15_26 : check v 8096
 ((RHBatch01ContourInputR00.row15.drop 416).take 16) ((RHBatch01ContourInputI00.row15.drop 416).take 16)=true ∧
 ((RHBatch01ContourInputR00.row15.drop 416).take 16).length=16 := by decide +kernel
theorem checked15_27 : check v 8112
 ((RHBatch01ContourInputR00.row15.drop 432).take 16) ((RHBatch01ContourInputI00.row15.drop 432).take 16)=true ∧
 ((RHBatch01ContourInputR00.row15.drop 432).take 16).length=16 := by decide +kernel
theorem checked15_28 : check v 8128
 ((RHBatch01ContourInputR00.row15.drop 448).take 16) ((RHBatch01ContourInputI00.row15.drop 448).take 16)=true ∧
 ((RHBatch01ContourInputR00.row15.drop 448).take 16).length=16 := by decide +kernel
theorem checked15_29 : check v 8144
 ((RHBatch01ContourInputR00.row15.drop 464).take 16) ((RHBatch01ContourInputI00.row15.drop 464).take 16)=true ∧
 ((RHBatch01ContourInputR00.row15.drop 464).take 16).length=16 := by decide +kernel
theorem checked15_30 : check v 8160
 ((RHBatch01ContourInputR00.row15.drop 480).take 16) ((RHBatch01ContourInputI00.row15.drop 480).take 16)=true ∧
 ((RHBatch01ContourInputR00.row15.drop 480).take 16).length=16 := by decide +kernel
theorem checked15_31 : check v 8176
 ((RHBatch01ContourInputR00.row15.drop 496).take 16) ((RHBatch01ContourInputI00.row15.drop 496).take 16)=true ∧
 ((RHBatch01ContourInputR00.row15.drop 496).take 16).length=16 := by decide +kernel
theorem checked16_00 : check v 8192
 ((RHBatch01ContourInputR00.row16.drop 0).take 16) ((RHBatch01ContourInputI00.row16.drop 0).take 16)=true ∧
 ((RHBatch01ContourInputR00.row16.drop 0).take 16).length=16 := by decide +kernel
theorem checked16_01 : check v 8208
 ((RHBatch01ContourInputR00.row16.drop 16).take 16) ((RHBatch01ContourInputI00.row16.drop 16).take 16)=true ∧
 ((RHBatch01ContourInputR00.row16.drop 16).take 16).length=16 := by decide +kernel
theorem checked16_02 : check v 8224
 ((RHBatch01ContourInputR00.row16.drop 32).take 16) ((RHBatch01ContourInputI00.row16.drop 32).take 16)=true ∧
 ((RHBatch01ContourInputR00.row16.drop 32).take 16).length=16 := by decide +kernel
theorem checked16_03 : check v 8240
 ((RHBatch01ContourInputR00.row16.drop 48).take 16) ((RHBatch01ContourInputI00.row16.drop 48).take 16)=true ∧
 ((RHBatch01ContourInputR00.row16.drop 48).take 16).length=16 := by decide +kernel
theorem checked16_04 : check v 8256
 ((RHBatch01ContourInputR00.row16.drop 64).take 16) ((RHBatch01ContourInputI00.row16.drop 64).take 16)=true ∧
 ((RHBatch01ContourInputR00.row16.drop 64).take 16).length=16 := by decide +kernel
theorem checked16_05 : check v 8272
 ((RHBatch01ContourInputR00.row16.drop 80).take 16) ((RHBatch01ContourInputI00.row16.drop 80).take 16)=true ∧
 ((RHBatch01ContourInputR00.row16.drop 80).take 16).length=16 := by decide +kernel
theorem checked16_06 : check v 8288
 ((RHBatch01ContourInputR00.row16.drop 96).take 16) ((RHBatch01ContourInputI00.row16.drop 96).take 16)=true ∧
 ((RHBatch01ContourInputR00.row16.drop 96).take 16).length=16 := by decide +kernel
theorem checked16_07 : check v 8304
 ((RHBatch01ContourInputR00.row16.drop 112).take 16) ((RHBatch01ContourInputI00.row16.drop 112).take 16)=true ∧
 ((RHBatch01ContourInputR00.row16.drop 112).take 16).length=16 := by decide +kernel
theorem checked16_08 : check v 8320
 ((RHBatch01ContourInputR00.row16.drop 128).take 16) ((RHBatch01ContourInputI00.row16.drop 128).take 16)=true ∧
 ((RHBatch01ContourInputR00.row16.drop 128).take 16).length=16 := by decide +kernel
theorem checked16_09 : check v 8336
 ((RHBatch01ContourInputR00.row16.drop 144).take 16) ((RHBatch01ContourInputI00.row16.drop 144).take 16)=true ∧
 ((RHBatch01ContourInputR00.row16.drop 144).take 16).length=16 := by decide +kernel
theorem checked16_10 : check v 8352
 ((RHBatch01ContourInputR00.row16.drop 160).take 16) ((RHBatch01ContourInputI00.row16.drop 160).take 16)=true ∧
 ((RHBatch01ContourInputR00.row16.drop 160).take 16).length=16 := by decide +kernel
theorem checked16_11 : check v 8368
 ((RHBatch01ContourInputR00.row16.drop 176).take 16) ((RHBatch01ContourInputI00.row16.drop 176).take 16)=true ∧
 ((RHBatch01ContourInputR00.row16.drop 176).take 16).length=16 := by decide +kernel
theorem checked16_12 : check v 8384
 ((RHBatch01ContourInputR00.row16.drop 192).take 16) ((RHBatch01ContourInputI00.row16.drop 192).take 16)=true ∧
 ((RHBatch01ContourInputR00.row16.drop 192).take 16).length=16 := by decide +kernel
theorem checked16_13 : check v 8400
 ((RHBatch01ContourInputR00.row16.drop 208).take 16) ((RHBatch01ContourInputI00.row16.drop 208).take 16)=true ∧
 ((RHBatch01ContourInputR00.row16.drop 208).take 16).length=16 := by decide +kernel
theorem checked16_14 : check v 8416
 ((RHBatch01ContourInputR00.row16.drop 224).take 16) ((RHBatch01ContourInputI00.row16.drop 224).take 16)=true ∧
 ((RHBatch01ContourInputR00.row16.drop 224).take 16).length=16 := by decide +kernel
theorem checked16_15 : check v 8432
 ((RHBatch01ContourInputR00.row16.drop 240).take 16) ((RHBatch01ContourInputI00.row16.drop 240).take 16)=true ∧
 ((RHBatch01ContourInputR00.row16.drop 240).take 16).length=16 := by decide +kernel
theorem checked16_16 : check v 8448
 ((RHBatch01ContourInputR00.row16.drop 256).take 16) ((RHBatch01ContourInputI00.row16.drop 256).take 16)=true ∧
 ((RHBatch01ContourInputR00.row16.drop 256).take 16).length=16 := by decide +kernel
theorem checked16_17 : check v 8464
 ((RHBatch01ContourInputR00.row16.drop 272).take 16) ((RHBatch01ContourInputI00.row16.drop 272).take 16)=true ∧
 ((RHBatch01ContourInputR00.row16.drop 272).take 16).length=16 := by decide +kernel
theorem checked16_18 : check v 8480
 ((RHBatch01ContourInputR00.row16.drop 288).take 16) ((RHBatch01ContourInputI00.row16.drop 288).take 16)=true ∧
 ((RHBatch01ContourInputR00.row16.drop 288).take 16).length=16 := by decide +kernel
theorem checked16_19 : check v 8496
 ((RHBatch01ContourInputR00.row16.drop 304).take 16) ((RHBatch01ContourInputI00.row16.drop 304).take 16)=true ∧
 ((RHBatch01ContourInputR00.row16.drop 304).take 16).length=16 := by decide +kernel
theorem checked16_20 : check v 8512
 ((RHBatch01ContourInputR00.row16.drop 320).take 16) ((RHBatch01ContourInputI00.row16.drop 320).take 16)=true ∧
 ((RHBatch01ContourInputR00.row16.drop 320).take 16).length=16 := by decide +kernel
theorem checked16_21 : check v 8528
 ((RHBatch01ContourInputR00.row16.drop 336).take 16) ((RHBatch01ContourInputI00.row16.drop 336).take 16)=true ∧
 ((RHBatch01ContourInputR00.row16.drop 336).take 16).length=16 := by decide +kernel
theorem checked16_22 : check v 8544
 ((RHBatch01ContourInputR00.row16.drop 352).take 16) ((RHBatch01ContourInputI00.row16.drop 352).take 16)=true ∧
 ((RHBatch01ContourInputR00.row16.drop 352).take 16).length=16 := by decide +kernel
theorem checked16_23 : check v 8560
 ((RHBatch01ContourInputR00.row16.drop 368).take 16) ((RHBatch01ContourInputI00.row16.drop 368).take 16)=true ∧
 ((RHBatch01ContourInputR00.row16.drop 368).take 16).length=16 := by decide +kernel
theorem checked16_24 : check v 8576
 ((RHBatch01ContourInputR00.row16.drop 384).take 16) ((RHBatch01ContourInputI00.row16.drop 384).take 16)=true ∧
 ((RHBatch01ContourInputR00.row16.drop 384).take 16).length=16 := by decide +kernel
theorem checked16_25 : check v 8592
 ((RHBatch01ContourInputR00.row16.drop 400).take 16) ((RHBatch01ContourInputI00.row16.drop 400).take 16)=true ∧
 ((RHBatch01ContourInputR00.row16.drop 400).take 16).length=16 := by decide +kernel
theorem checked16_26 : check v 8608
 ((RHBatch01ContourInputR00.row16.drop 416).take 16) ((RHBatch01ContourInputI00.row16.drop 416).take 16)=true ∧
 ((RHBatch01ContourInputR00.row16.drop 416).take 16).length=16 := by decide +kernel
theorem checked16_27 : check v 8624
 ((RHBatch01ContourInputR00.row16.drop 432).take 16) ((RHBatch01ContourInputI00.row16.drop 432).take 16)=true ∧
 ((RHBatch01ContourInputR00.row16.drop 432).take 16).length=16 := by decide +kernel
theorem checked16_28 : check v 8640
 ((RHBatch01ContourInputR00.row16.drop 448).take 16) ((RHBatch01ContourInputI00.row16.drop 448).take 16)=true ∧
 ((RHBatch01ContourInputR00.row16.drop 448).take 16).length=16 := by decide +kernel
theorem checked16_29 : check v 8656
 ((RHBatch01ContourInputR00.row16.drop 464).take 16) ((RHBatch01ContourInputI00.row16.drop 464).take 16)=true ∧
 ((RHBatch01ContourInputR00.row16.drop 464).take 16).length=16 := by decide +kernel
theorem checked16_30 : check v 8672
 ((RHBatch01ContourInputR00.row16.drop 480).take 16) ((RHBatch01ContourInputI00.row16.drop 480).take 16)=true ∧
 ((RHBatch01ContourInputR00.row16.drop 480).take 16).length=16 := by decide +kernel
theorem checked16_31 : check v 8688
 ((RHBatch01ContourInputR00.row16.drop 496).take 16) ((RHBatch01ContourInputI00.row16.drop 496).take 16)=true ∧
 ((RHBatch01ContourInputR00.row16.drop 496).take 16).length=16 := by decide +kernel
theorem checked17_00 : check v 8704
 ((RHBatch01ContourInputR00.row17.drop 0).take 16) ((RHBatch01ContourInputI00.row17.drop 0).take 16)=true ∧
 ((RHBatch01ContourInputR00.row17.drop 0).take 16).length=16 := by decide +kernel
theorem checked17_01 : check v 8720
 ((RHBatch01ContourInputR00.row17.drop 16).take 16) ((RHBatch01ContourInputI00.row17.drop 16).take 16)=true ∧
 ((RHBatch01ContourInputR00.row17.drop 16).take 16).length=16 := by decide +kernel
theorem checked17_02 : check v 8736
 ((RHBatch01ContourInputR00.row17.drop 32).take 16) ((RHBatch01ContourInputI00.row17.drop 32).take 16)=true ∧
 ((RHBatch01ContourInputR00.row17.drop 32).take 16).length=16 := by decide +kernel
theorem checked17_03 : check v 8752
 ((RHBatch01ContourInputR00.row17.drop 48).take 16) ((RHBatch01ContourInputI00.row17.drop 48).take 16)=true ∧
 ((RHBatch01ContourInputR00.row17.drop 48).take 16).length=16 := by decide +kernel
theorem checked17_04 : check v 8768
 ((RHBatch01ContourInputR00.row17.drop 64).take 16) ((RHBatch01ContourInputI00.row17.drop 64).take 16)=true ∧
 ((RHBatch01ContourInputR00.row17.drop 64).take 16).length=16 := by decide +kernel
theorem checked17_05 : check v 8784
 ((RHBatch01ContourInputR00.row17.drop 80).take 16) ((RHBatch01ContourInputI00.row17.drop 80).take 16)=true ∧
 ((RHBatch01ContourInputR00.row17.drop 80).take 16).length=16 := by decide +kernel
theorem checked17_06 : check v 8800
 ((RHBatch01ContourInputR00.row17.drop 96).take 16) ((RHBatch01ContourInputI00.row17.drop 96).take 16)=true ∧
 ((RHBatch01ContourInputR00.row17.drop 96).take 16).length=16 := by decide +kernel
theorem checked17_07 : check v 8816
 ((RHBatch01ContourInputR00.row17.drop 112).take 16) ((RHBatch01ContourInputI00.row17.drop 112).take 16)=true ∧
 ((RHBatch01ContourInputR00.row17.drop 112).take 16).length=16 := by decide +kernel
theorem checked17_08 : check v 8832
 ((RHBatch01ContourInputR00.row17.drop 128).take 16) ((RHBatch01ContourInputI00.row17.drop 128).take 16)=true ∧
 ((RHBatch01ContourInputR00.row17.drop 128).take 16).length=16 := by decide +kernel
theorem checked17_09 : check v 8848
 ((RHBatch01ContourInputR00.row17.drop 144).take 16) ((RHBatch01ContourInputI00.row17.drop 144).take 16)=true ∧
 ((RHBatch01ContourInputR00.row17.drop 144).take 16).length=16 := by decide +kernel
theorem checked17_10 : check v 8864
 ((RHBatch01ContourInputR00.row17.drop 160).take 16) ((RHBatch01ContourInputI00.row17.drop 160).take 16)=true ∧
 ((RHBatch01ContourInputR00.row17.drop 160).take 16).length=16 := by decide +kernel
theorem checked17_11 : check v 8880
 ((RHBatch01ContourInputR00.row17.drop 176).take 16) ((RHBatch01ContourInputI00.row17.drop 176).take 16)=true ∧
 ((RHBatch01ContourInputR00.row17.drop 176).take 16).length=16 := by decide +kernel
theorem checked17_12 : check v 8896
 ((RHBatch01ContourInputR00.row17.drop 192).take 16) ((RHBatch01ContourInputI00.row17.drop 192).take 16)=true ∧
 ((RHBatch01ContourInputR00.row17.drop 192).take 16).length=16 := by decide +kernel
theorem checked17_13 : check v 8912
 ((RHBatch01ContourInputR00.row17.drop 208).take 16) ((RHBatch01ContourInputI00.row17.drop 208).take 16)=true ∧
 ((RHBatch01ContourInputR00.row17.drop 208).take 16).length=16 := by decide +kernel
theorem checked17_14 : check v 8928
 ((RHBatch01ContourInputR00.row17.drop 224).take 16) ((RHBatch01ContourInputI00.row17.drop 224).take 16)=true ∧
 ((RHBatch01ContourInputR00.row17.drop 224).take 16).length=16 := by decide +kernel
theorem checked17_15 : check v 8944
 ((RHBatch01ContourInputR00.row17.drop 240).take 16) ((RHBatch01ContourInputI00.row17.drop 240).take 16)=true ∧
 ((RHBatch01ContourInputR00.row17.drop 240).take 16).length=16 := by decide +kernel
theorem checked17_16 : check v 8960
 ((RHBatch01ContourInputR00.row17.drop 256).take 16) ((RHBatch01ContourInputI00.row17.drop 256).take 16)=true ∧
 ((RHBatch01ContourInputR00.row17.drop 256).take 16).length=16 := by decide +kernel
theorem checked17_17 : check v 8976
 ((RHBatch01ContourInputR00.row17.drop 272).take 16) ((RHBatch01ContourInputI00.row17.drop 272).take 16)=true ∧
 ((RHBatch01ContourInputR00.row17.drop 272).take 16).length=16 := by decide +kernel
theorem checked17_18 : check v 8992
 ((RHBatch01ContourInputR00.row17.drop 288).take 16) ((RHBatch01ContourInputI00.row17.drop 288).take 16)=true ∧
 ((RHBatch01ContourInputR00.row17.drop 288).take 16).length=16 := by decide +kernel
theorem checked17_19 : check v 9008
 ((RHBatch01ContourInputR00.row17.drop 304).take 16) ((RHBatch01ContourInputI00.row17.drop 304).take 16)=true ∧
 ((RHBatch01ContourInputR00.row17.drop 304).take 16).length=16 := by decide +kernel
theorem checked17_20 : check v 9024
 ((RHBatch01ContourInputR00.row17.drop 320).take 16) ((RHBatch01ContourInputI00.row17.drop 320).take 16)=true ∧
 ((RHBatch01ContourInputR00.row17.drop 320).take 16).length=16 := by decide +kernel
theorem checked17_21 : check v 9040
 ((RHBatch01ContourInputR00.row17.drop 336).take 16) ((RHBatch01ContourInputI00.row17.drop 336).take 16)=true ∧
 ((RHBatch01ContourInputR00.row17.drop 336).take 16).length=16 := by decide +kernel
theorem checked17_22 : check v 9056
 ((RHBatch01ContourInputR00.row17.drop 352).take 16) ((RHBatch01ContourInputI00.row17.drop 352).take 16)=true ∧
 ((RHBatch01ContourInputR00.row17.drop 352).take 16).length=16 := by decide +kernel
theorem checked17_23 : check v 9072
 ((RHBatch01ContourInputR00.row17.drop 368).take 16) ((RHBatch01ContourInputI00.row17.drop 368).take 16)=true ∧
 ((RHBatch01ContourInputR00.row17.drop 368).take 16).length=16 := by decide +kernel
theorem checked17_24 : check v 9088
 ((RHBatch01ContourInputR00.row17.drop 384).take 16) ((RHBatch01ContourInputI00.row17.drop 384).take 16)=true ∧
 ((RHBatch01ContourInputR00.row17.drop 384).take 16).length=16 := by decide +kernel
theorem checked17_25 : check v 9104
 ((RHBatch01ContourInputR00.row17.drop 400).take 16) ((RHBatch01ContourInputI00.row17.drop 400).take 16)=true ∧
 ((RHBatch01ContourInputR00.row17.drop 400).take 16).length=16 := by decide +kernel
theorem checked17_26 : check v 9120
 ((RHBatch01ContourInputR00.row17.drop 416).take 16) ((RHBatch01ContourInputI00.row17.drop 416).take 16)=true ∧
 ((RHBatch01ContourInputR00.row17.drop 416).take 16).length=16 := by decide +kernel
theorem checked17_27 : check v 9136
 ((RHBatch01ContourInputR00.row17.drop 432).take 16) ((RHBatch01ContourInputI00.row17.drop 432).take 16)=true ∧
 ((RHBatch01ContourInputR00.row17.drop 432).take 16).length=16 := by decide +kernel
theorem checked17_28 : check v 9152
 ((RHBatch01ContourInputR00.row17.drop 448).take 16) ((RHBatch01ContourInputI00.row17.drop 448).take 16)=true ∧
 ((RHBatch01ContourInputR00.row17.drop 448).take 16).length=16 := by decide +kernel
theorem checked17_29 : check v 9168
 ((RHBatch01ContourInputR00.row17.drop 464).take 16) ((RHBatch01ContourInputI00.row17.drop 464).take 16)=true ∧
 ((RHBatch01ContourInputR00.row17.drop 464).take 16).length=16 := by decide +kernel
theorem checked17_30 : check v 9184
 ((RHBatch01ContourInputR00.row17.drop 480).take 16) ((RHBatch01ContourInputI00.row17.drop 480).take 16)=true ∧
 ((RHBatch01ContourInputR00.row17.drop 480).take 16).length=16 := by decide +kernel
theorem checked17_31 : check v 9200
 ((RHBatch01ContourInputR00.row17.drop 496).take 16) ((RHBatch01ContourInputI00.row17.drop 496).take 16)=true ∧
 ((RHBatch01ContourInputR00.row17.drop 496).take 16).length=16 := by decide +kernel
theorem checked18_00 : check v 9216
 ((RHBatch01ContourInputR00.row18.drop 0).take 16) ((RHBatch01ContourInputI00.row18.drop 0).take 16)=true ∧
 ((RHBatch01ContourInputR00.row18.drop 0).take 16).length=16 := by decide +kernel
theorem checked18_01 : check v 9232
 ((RHBatch01ContourInputR00.row18.drop 16).take 16) ((RHBatch01ContourInputI00.row18.drop 16).take 16)=true ∧
 ((RHBatch01ContourInputR00.row18.drop 16).take 16).length=16 := by decide +kernel
theorem checked18_02 : check v 9248
 ((RHBatch01ContourInputR00.row18.drop 32).take 16) ((RHBatch01ContourInputI00.row18.drop 32).take 16)=true ∧
 ((RHBatch01ContourInputR00.row18.drop 32).take 16).length=16 := by decide +kernel
theorem checked18_03 : check v 9264
 ((RHBatch01ContourInputR00.row18.drop 48).take 16) ((RHBatch01ContourInputI00.row18.drop 48).take 16)=true ∧
 ((RHBatch01ContourInputR00.row18.drop 48).take 16).length=16 := by decide +kernel
theorem checked18_04 : check v 9280
 ((RHBatch01ContourInputR00.row18.drop 64).take 16) ((RHBatch01ContourInputI00.row18.drop 64).take 16)=true ∧
 ((RHBatch01ContourInputR00.row18.drop 64).take 16).length=16 := by decide +kernel
theorem checked18_05 : check v 9296
 ((RHBatch01ContourInputR00.row18.drop 80).take 16) ((RHBatch01ContourInputI00.row18.drop 80).take 16)=true ∧
 ((RHBatch01ContourInputR00.row18.drop 80).take 16).length=16 := by decide +kernel
theorem checked18_06 : check v 9312
 ((RHBatch01ContourInputR00.row18.drop 96).take 16) ((RHBatch01ContourInputI00.row18.drop 96).take 16)=true ∧
 ((RHBatch01ContourInputR00.row18.drop 96).take 16).length=16 := by decide +kernel
theorem checked18_07 : check v 9328
 ((RHBatch01ContourInputR00.row18.drop 112).take 16) ((RHBatch01ContourInputI00.row18.drop 112).take 16)=true ∧
 ((RHBatch01ContourInputR00.row18.drop 112).take 16).length=16 := by decide +kernel
theorem checked18_08 : check v 9344
 ((RHBatch01ContourInputR00.row18.drop 128).take 16) ((RHBatch01ContourInputI00.row18.drop 128).take 16)=true ∧
 ((RHBatch01ContourInputR00.row18.drop 128).take 16).length=16 := by decide +kernel
theorem checked18_09 : check v 9360
 ((RHBatch01ContourInputR00.row18.drop 144).take 16) ((RHBatch01ContourInputI00.row18.drop 144).take 16)=true ∧
 ((RHBatch01ContourInputR00.row18.drop 144).take 16).length=16 := by decide +kernel
theorem checked18_10 : check v 9376
 ((RHBatch01ContourInputR00.row18.drop 160).take 16) ((RHBatch01ContourInputI00.row18.drop 160).take 16)=true ∧
 ((RHBatch01ContourInputR00.row18.drop 160).take 16).length=16 := by decide +kernel
theorem checked18_11 : check v 9392
 ((RHBatch01ContourInputR00.row18.drop 176).take 16) ((RHBatch01ContourInputI00.row18.drop 176).take 16)=true ∧
 ((RHBatch01ContourInputR00.row18.drop 176).take 16).length=16 := by decide +kernel
theorem checked18_12 : check v 9408
 ((RHBatch01ContourInputR00.row18.drop 192).take 16) ((RHBatch01ContourInputI00.row18.drop 192).take 16)=true ∧
 ((RHBatch01ContourInputR00.row18.drop 192).take 16).length=16 := by decide +kernel
theorem checked18_13 : check v 9424
 ((RHBatch01ContourInputR00.row18.drop 208).take 16) ((RHBatch01ContourInputI00.row18.drop 208).take 16)=true ∧
 ((RHBatch01ContourInputR00.row18.drop 208).take 16).length=16 := by decide +kernel
theorem checked18_14 : check v 9440
 ((RHBatch01ContourInputR00.row18.drop 224).take 16) ((RHBatch01ContourInputI00.row18.drop 224).take 16)=true ∧
 ((RHBatch01ContourInputR00.row18.drop 224).take 16).length=16 := by decide +kernel
theorem checked18_15 : check v 9456
 ((RHBatch01ContourInputR00.row18.drop 240).take 16) ((RHBatch01ContourInputI00.row18.drop 240).take 16)=true ∧
 ((RHBatch01ContourInputR00.row18.drop 240).take 16).length=16 := by decide +kernel
theorem checked18_16 : check v 9472
 ((RHBatch01ContourInputR00.row18.drop 256).take 16) ((RHBatch01ContourInputI00.row18.drop 256).take 16)=true ∧
 ((RHBatch01ContourInputR00.row18.drop 256).take 16).length=16 := by decide +kernel
theorem checked18_17 : check v 9488
 ((RHBatch01ContourInputR00.row18.drop 272).take 16) ((RHBatch01ContourInputI00.row18.drop 272).take 16)=true ∧
 ((RHBatch01ContourInputR00.row18.drop 272).take 16).length=16 := by decide +kernel
theorem checked18_18 : check v 9504
 ((RHBatch01ContourInputR00.row18.drop 288).take 16) ((RHBatch01ContourInputI00.row18.drop 288).take 16)=true ∧
 ((RHBatch01ContourInputR00.row18.drop 288).take 16).length=16 := by decide +kernel
theorem checked18_19 : check v 9520
 ((RHBatch01ContourInputR00.row18.drop 304).take 16) ((RHBatch01ContourInputI00.row18.drop 304).take 16)=true ∧
 ((RHBatch01ContourInputR00.row18.drop 304).take 16).length=16 := by decide +kernel
theorem checked18_20 : check v 9536
 ((RHBatch01ContourInputR00.row18.drop 320).take 16) ((RHBatch01ContourInputI00.row18.drop 320).take 16)=true ∧
 ((RHBatch01ContourInputR00.row18.drop 320).take 16).length=16 := by decide +kernel
theorem checked18_21 : check v 9552
 ((RHBatch01ContourInputR00.row18.drop 336).take 16) ((RHBatch01ContourInputI00.row18.drop 336).take 16)=true ∧
 ((RHBatch01ContourInputR00.row18.drop 336).take 16).length=16 := by decide +kernel
theorem checked18_22 : check v 9568
 ((RHBatch01ContourInputR00.row18.drop 352).take 16) ((RHBatch01ContourInputI00.row18.drop 352).take 16)=true ∧
 ((RHBatch01ContourInputR00.row18.drop 352).take 16).length=16 := by decide +kernel
theorem checked18_23 : check v 9584
 ((RHBatch01ContourInputR00.row18.drop 368).take 16) ((RHBatch01ContourInputI00.row18.drop 368).take 16)=true ∧
 ((RHBatch01ContourInputR00.row18.drop 368).take 16).length=16 := by decide +kernel
theorem checked18_24 : check v 9600
 ((RHBatch01ContourInputR00.row18.drop 384).take 16) ((RHBatch01ContourInputI00.row18.drop 384).take 16)=true ∧
 ((RHBatch01ContourInputR00.row18.drop 384).take 16).length=16 := by decide +kernel
theorem checked18_25 : check v 9616
 ((RHBatch01ContourInputR00.row18.drop 400).take 16) ((RHBatch01ContourInputI00.row18.drop 400).take 16)=true ∧
 ((RHBatch01ContourInputR00.row18.drop 400).take 16).length=16 := by decide +kernel
theorem checked18_26 : check v 9632
 ((RHBatch01ContourInputR00.row18.drop 416).take 16) ((RHBatch01ContourInputI00.row18.drop 416).take 16)=true ∧
 ((RHBatch01ContourInputR00.row18.drop 416).take 16).length=16 := by decide +kernel
theorem checked18_27 : check v 9648
 ((RHBatch01ContourInputR00.row18.drop 432).take 16) ((RHBatch01ContourInputI00.row18.drop 432).take 16)=true ∧
 ((RHBatch01ContourInputR00.row18.drop 432).take 16).length=16 := by decide +kernel
theorem checked18_28 : check v 9664
 ((RHBatch01ContourInputR00.row18.drop 448).take 16) ((RHBatch01ContourInputI00.row18.drop 448).take 16)=true ∧
 ((RHBatch01ContourInputR00.row18.drop 448).take 16).length=16 := by decide +kernel
theorem checked18_29 : check v 9680
 ((RHBatch01ContourInputR00.row18.drop 464).take 16) ((RHBatch01ContourInputI00.row18.drop 464).take 16)=true ∧
 ((RHBatch01ContourInputR00.row18.drop 464).take 16).length=16 := by decide +kernel
theorem checked18_30 : check v 9696
 ((RHBatch01ContourInputR00.row18.drop 480).take 16) ((RHBatch01ContourInputI00.row18.drop 480).take 16)=true ∧
 ((RHBatch01ContourInputR00.row18.drop 480).take 16).length=16 := by decide +kernel
theorem checked18_31 : check v 9712
 ((RHBatch01ContourInputR00.row18.drop 496).take 16) ((RHBatch01ContourInputI00.row18.drop 496).take 16)=true ∧
 ((RHBatch01ContourInputR00.row18.drop 496).take 16).length=16 := by decide +kernel
theorem checked19_00 : check v 9728
 ((RHBatch01ContourInputR00.row19.drop 0).take 16) ((RHBatch01ContourInputI00.row19.drop 0).take 16)=true ∧
 ((RHBatch01ContourInputR00.row19.drop 0).take 16).length=16 := by decide +kernel
theorem checked19_01 : check v 9744
 ((RHBatch01ContourInputR00.row19.drop 16).take 16) ((RHBatch01ContourInputI00.row19.drop 16).take 16)=true ∧
 ((RHBatch01ContourInputR00.row19.drop 16).take 16).length=16 := by decide +kernel
theorem checked19_02 : check v 9760
 ((RHBatch01ContourInputR00.row19.drop 32).take 16) ((RHBatch01ContourInputI00.row19.drop 32).take 16)=true ∧
 ((RHBatch01ContourInputR00.row19.drop 32).take 16).length=16 := by decide +kernel
theorem checked19_03 : check v 9776
 ((RHBatch01ContourInputR00.row19.drop 48).take 16) ((RHBatch01ContourInputI00.row19.drop 48).take 16)=true ∧
 ((RHBatch01ContourInputR00.row19.drop 48).take 16).length=16 := by decide +kernel
theorem checked19_04 : check v 9792
 ((RHBatch01ContourInputR00.row19.drop 64).take 16) ((RHBatch01ContourInputI00.row19.drop 64).take 16)=true ∧
 ((RHBatch01ContourInputR00.row19.drop 64).take 16).length=16 := by decide +kernel
theorem checked19_05 : check v 9808
 ((RHBatch01ContourInputR00.row19.drop 80).take 16) ((RHBatch01ContourInputI00.row19.drop 80).take 16)=true ∧
 ((RHBatch01ContourInputR00.row19.drop 80).take 16).length=16 := by decide +kernel
theorem checked19_06 : check v 9824
 ((RHBatch01ContourInputR00.row19.drop 96).take 16) ((RHBatch01ContourInputI00.row19.drop 96).take 16)=true ∧
 ((RHBatch01ContourInputR00.row19.drop 96).take 16).length=16 := by decide +kernel
theorem checked19_07 : check v 9840
 ((RHBatch01ContourInputR00.row19.drop 112).take 16) ((RHBatch01ContourInputI00.row19.drop 112).take 16)=true ∧
 ((RHBatch01ContourInputR00.row19.drop 112).take 16).length=16 := by decide +kernel
theorem checked19_08 : check v 9856
 ((RHBatch01ContourInputR00.row19.drop 128).take 16) ((RHBatch01ContourInputI00.row19.drop 128).take 16)=true ∧
 ((RHBatch01ContourInputR00.row19.drop 128).take 16).length=16 := by decide +kernel
theorem checked19_09 : check v 9872
 ((RHBatch01ContourInputR00.row19.drop 144).take 16) ((RHBatch01ContourInputI00.row19.drop 144).take 16)=true ∧
 ((RHBatch01ContourInputR00.row19.drop 144).take 16).length=16 := by decide +kernel
theorem checked19_10 : check v 9888
 ((RHBatch01ContourInputR00.row19.drop 160).take 16) ((RHBatch01ContourInputI00.row19.drop 160).take 16)=true ∧
 ((RHBatch01ContourInputR00.row19.drop 160).take 16).length=16 := by decide +kernel
theorem checked19_11 : check v 9904
 ((RHBatch01ContourInputR00.row19.drop 176).take 16) ((RHBatch01ContourInputI00.row19.drop 176).take 16)=true ∧
 ((RHBatch01ContourInputR00.row19.drop 176).take 16).length=16 := by decide +kernel
theorem checked19_12 : check v 9920
 ((RHBatch01ContourInputR00.row19.drop 192).take 16) ((RHBatch01ContourInputI00.row19.drop 192).take 16)=true ∧
 ((RHBatch01ContourInputR00.row19.drop 192).take 16).length=16 := by decide +kernel
theorem checked19_13 : check v 9936
 ((RHBatch01ContourInputR00.row19.drop 208).take 16) ((RHBatch01ContourInputI00.row19.drop 208).take 16)=true ∧
 ((RHBatch01ContourInputR00.row19.drop 208).take 16).length=16 := by decide +kernel
theorem checked19_14 : check v 9952
 ((RHBatch01ContourInputR00.row19.drop 224).take 16) ((RHBatch01ContourInputI00.row19.drop 224).take 16)=true ∧
 ((RHBatch01ContourInputR00.row19.drop 224).take 16).length=16 := by decide +kernel
theorem checked19_15 : check v 9968
 ((RHBatch01ContourInputR00.row19.drop 240).take 16) ((RHBatch01ContourInputI00.row19.drop 240).take 16)=true ∧
 ((RHBatch01ContourInputR00.row19.drop 240).take 16).length=16 := by decide +kernel
theorem checked19_16 : check v 9984
 ((RHBatch01ContourInputR00.row19.drop 256).take 16) ((RHBatch01ContourInputI00.row19.drop 256).take 16)=true ∧
 ((RHBatch01ContourInputR00.row19.drop 256).take 16).length=16 := by decide +kernel
theorem checked19_17 : check v 10000
 ((RHBatch01ContourInputR00.row19.drop 272).take 16) ((RHBatch01ContourInputI00.row19.drop 272).take 16)=true ∧
 ((RHBatch01ContourInputR00.row19.drop 272).take 16).length=16 := by decide +kernel
theorem checked19_18 : check v 10016
 ((RHBatch01ContourInputR00.row19.drop 288).take 16) ((RHBatch01ContourInputI00.row19.drop 288).take 16)=true ∧
 ((RHBatch01ContourInputR00.row19.drop 288).take 16).length=16 := by decide +kernel
theorem checked19_19 : check v 10032
 ((RHBatch01ContourInputR00.row19.drop 304).take 16) ((RHBatch01ContourInputI00.row19.drop 304).take 16)=true ∧
 ((RHBatch01ContourInputR00.row19.drop 304).take 16).length=16 := by decide +kernel
theorem checked19_20 : check v 10048
 ((RHBatch01ContourInputR00.row19.drop 320).take 16) ((RHBatch01ContourInputI00.row19.drop 320).take 16)=true ∧
 ((RHBatch01ContourInputR00.row19.drop 320).take 16).length=16 := by decide +kernel
theorem checked19_21 : check v 10064
 ((RHBatch01ContourInputR00.row19.drop 336).take 16) ((RHBatch01ContourInputI00.row19.drop 336).take 16)=true ∧
 ((RHBatch01ContourInputR00.row19.drop 336).take 16).length=16 := by decide +kernel
theorem checked19_22 : check v 10080
 ((RHBatch01ContourInputR00.row19.drop 352).take 16) ((RHBatch01ContourInputI00.row19.drop 352).take 16)=true ∧
 ((RHBatch01ContourInputR00.row19.drop 352).take 16).length=16 := by decide +kernel
theorem checked19_23 : check v 10096
 ((RHBatch01ContourInputR00.row19.drop 368).take 16) ((RHBatch01ContourInputI00.row19.drop 368).take 16)=true ∧
 ((RHBatch01ContourInputR00.row19.drop 368).take 16).length=16 := by decide +kernel
theorem checked19_24 : check v 10112
 ((RHBatch01ContourInputR00.row19.drop 384).take 16) ((RHBatch01ContourInputI00.row19.drop 384).take 16)=true ∧
 ((RHBatch01ContourInputR00.row19.drop 384).take 16).length=16 := by decide +kernel
theorem checked19_25 : check v 10128
 ((RHBatch01ContourInputR00.row19.drop 400).take 16) ((RHBatch01ContourInputI00.row19.drop 400).take 16)=true ∧
 ((RHBatch01ContourInputR00.row19.drop 400).take 16).length=16 := by decide +kernel
theorem checked19_26 : check v 10144
 ((RHBatch01ContourInputR00.row19.drop 416).take 16) ((RHBatch01ContourInputI00.row19.drop 416).take 16)=true ∧
 ((RHBatch01ContourInputR00.row19.drop 416).take 16).length=16 := by decide +kernel
theorem checked19_27 : check v 10160
 ((RHBatch01ContourInputR00.row19.drop 432).take 16) ((RHBatch01ContourInputI00.row19.drop 432).take 16)=true ∧
 ((RHBatch01ContourInputR00.row19.drop 432).take 16).length=16 := by decide +kernel
theorem checked19_28 : check v 10176
 ((RHBatch01ContourInputR00.row19.drop 448).take 16) ((RHBatch01ContourInputI00.row19.drop 448).take 16)=true ∧
 ((RHBatch01ContourInputR00.row19.drop 448).take 16).length=16 := by decide +kernel
theorem checked19_29 : check v 10192
 ((RHBatch01ContourInputR00.row19.drop 464).take 16) ((RHBatch01ContourInputI00.row19.drop 464).take 16)=true ∧
 ((RHBatch01ContourInputR00.row19.drop 464).take 16).length=16 := by decide +kernel
theorem checked19_30 : check v 10208
 ((RHBatch01ContourInputR00.row19.drop 480).take 16) ((RHBatch01ContourInputI00.row19.drop 480).take 16)=true ∧
 ((RHBatch01ContourInputR00.row19.drop 480).take 16).length=16 := by decide +kernel
theorem checked19_31 : check v 10224
 ((RHBatch01ContourInputR00.row19.drop 496).take 16) ((RHBatch01ContourInputI00.row19.drop 496).take 16)=true ∧
 ((RHBatch01ContourInputR00.row19.drop 496).take 16).length=16 := by decide +kernel
theorem checked20_00 : check v 10240
 ((RHBatch01ContourInputR00.row20.drop 0).take 16) ((RHBatch01ContourInputI00.row20.drop 0).take 16)=true ∧
 ((RHBatch01ContourInputR00.row20.drop 0).take 16).length=16 := by decide +kernel
theorem checked20_01 : check v 10256
 ((RHBatch01ContourInputR00.row20.drop 16).take 16) ((RHBatch01ContourInputI00.row20.drop 16).take 16)=true ∧
 ((RHBatch01ContourInputR00.row20.drop 16).take 16).length=16 := by decide +kernel
theorem checked20_02 : check v 10272
 ((RHBatch01ContourInputR00.row20.drop 32).take 16) ((RHBatch01ContourInputI00.row20.drop 32).take 16)=true ∧
 ((RHBatch01ContourInputR00.row20.drop 32).take 16).length=16 := by decide +kernel
theorem checked20_03 : check v 10288
 ((RHBatch01ContourInputR00.row20.drop 48).take 16) ((RHBatch01ContourInputI00.row20.drop 48).take 16)=true ∧
 ((RHBatch01ContourInputR00.row20.drop 48).take 16).length=16 := by decide +kernel
theorem checked20_04 : check v 10304
 ((RHBatch01ContourInputR00.row20.drop 64).take 16) ((RHBatch01ContourInputI00.row20.drop 64).take 16)=true ∧
 ((RHBatch01ContourInputR00.row20.drop 64).take 16).length=16 := by decide +kernel
theorem checked20_05 : check v 10320
 ((RHBatch01ContourInputR00.row20.drop 80).take 16) ((RHBatch01ContourInputI00.row20.drop 80).take 16)=true ∧
 ((RHBatch01ContourInputR00.row20.drop 80).take 16).length=16 := by decide +kernel
theorem checked20_06 : check v 10336
 ((RHBatch01ContourInputR00.row20.drop 96).take 16) ((RHBatch01ContourInputI00.row20.drop 96).take 16)=true ∧
 ((RHBatch01ContourInputR00.row20.drop 96).take 16).length=16 := by decide +kernel
theorem checked20_07 : check v 10352
 ((RHBatch01ContourInputR00.row20.drop 112).take 16) ((RHBatch01ContourInputI00.row20.drop 112).take 16)=true ∧
 ((RHBatch01ContourInputR00.row20.drop 112).take 16).length=16 := by decide +kernel
theorem checked20_08 : check v 10368
 ((RHBatch01ContourInputR00.row20.drop 128).take 16) ((RHBatch01ContourInputI00.row20.drop 128).take 16)=true ∧
 ((RHBatch01ContourInputR00.row20.drop 128).take 16).length=16 := by decide +kernel
theorem checked20_09 : check v 10384
 ((RHBatch01ContourInputR00.row20.drop 144).take 16) ((RHBatch01ContourInputI00.row20.drop 144).take 16)=true ∧
 ((RHBatch01ContourInputR00.row20.drop 144).take 16).length=16 := by decide +kernel
theorem checked20_10 : check v 10400
 ((RHBatch01ContourInputR00.row20.drop 160).take 16) ((RHBatch01ContourInputI00.row20.drop 160).take 16)=true ∧
 ((RHBatch01ContourInputR00.row20.drop 160).take 16).length=16 := by decide +kernel
theorem checked20_11 : check v 10416
 ((RHBatch01ContourInputR00.row20.drop 176).take 16) ((RHBatch01ContourInputI00.row20.drop 176).take 16)=true ∧
 ((RHBatch01ContourInputR00.row20.drop 176).take 16).length=16 := by decide +kernel
theorem checked20_12 : check v 10432
 ((RHBatch01ContourInputR00.row20.drop 192).take 16) ((RHBatch01ContourInputI00.row20.drop 192).take 16)=true ∧
 ((RHBatch01ContourInputR00.row20.drop 192).take 16).length=16 := by decide +kernel
theorem checked20_13 : check v 10448
 ((RHBatch01ContourInputR00.row20.drop 208).take 16) ((RHBatch01ContourInputI00.row20.drop 208).take 16)=true ∧
 ((RHBatch01ContourInputR00.row20.drop 208).take 16).length=16 := by decide +kernel
theorem checked20_14 : check v 10464
 ((RHBatch01ContourInputR00.row20.drop 224).take 16) ((RHBatch01ContourInputI00.row20.drop 224).take 16)=true ∧
 ((RHBatch01ContourInputR00.row20.drop 224).take 16).length=16 := by decide +kernel
theorem checked20_15 : check v 10480
 ((RHBatch01ContourInputR00.row20.drop 240).take 16) ((RHBatch01ContourInputI00.row20.drop 240).take 16)=true ∧
 ((RHBatch01ContourInputR00.row20.drop 240).take 16).length=16 := by decide +kernel
theorem checked20_16 : check v 10496
 ((RHBatch01ContourInputR00.row20.drop 256).take 16) ((RHBatch01ContourInputI00.row20.drop 256).take 16)=true ∧
 ((RHBatch01ContourInputR00.row20.drop 256).take 16).length=16 := by decide +kernel
theorem checked20_17 : check v 10512
 ((RHBatch01ContourInputR00.row20.drop 272).take 16) ((RHBatch01ContourInputI00.row20.drop 272).take 16)=true ∧
 ((RHBatch01ContourInputR00.row20.drop 272).take 16).length=16 := by decide +kernel
theorem checked20_18 : check v 10528
 ((RHBatch01ContourInputR00.row20.drop 288).take 16) ((RHBatch01ContourInputI00.row20.drop 288).take 16)=true ∧
 ((RHBatch01ContourInputR00.row20.drop 288).take 16).length=16 := by decide +kernel
theorem checked20_19 : check v 10544
 ((RHBatch01ContourInputR00.row20.drop 304).take 16) ((RHBatch01ContourInputI00.row20.drop 304).take 16)=true ∧
 ((RHBatch01ContourInputR00.row20.drop 304).take 16).length=16 := by decide +kernel
theorem checked20_20 : check v 10560
 ((RHBatch01ContourInputR00.row20.drop 320).take 16) ((RHBatch01ContourInputI00.row20.drop 320).take 16)=true ∧
 ((RHBatch01ContourInputR00.row20.drop 320).take 16).length=16 := by decide +kernel
theorem checked20_21 : check v 10576
 ((RHBatch01ContourInputR00.row20.drop 336).take 16) ((RHBatch01ContourInputI00.row20.drop 336).take 16)=true ∧
 ((RHBatch01ContourInputR00.row20.drop 336).take 16).length=16 := by decide +kernel
theorem checked20_22 : check v 10592
 ((RHBatch01ContourInputR00.row20.drop 352).take 16) ((RHBatch01ContourInputI00.row20.drop 352).take 16)=true ∧
 ((RHBatch01ContourInputR00.row20.drop 352).take 16).length=16 := by decide +kernel
theorem checked20_23 : check v 10608
 ((RHBatch01ContourInputR00.row20.drop 368).take 16) ((RHBatch01ContourInputI00.row20.drop 368).take 16)=true ∧
 ((RHBatch01ContourInputR00.row20.drop 368).take 16).length=16 := by decide +kernel
theorem checked20_24 : check v 10624
 ((RHBatch01ContourInputR00.row20.drop 384).take 16) ((RHBatch01ContourInputI00.row20.drop 384).take 16)=true ∧
 ((RHBatch01ContourInputR00.row20.drop 384).take 16).length=16 := by decide +kernel
theorem checked20_25 : check v 10640
 ((RHBatch01ContourInputR00.row20.drop 400).take 16) ((RHBatch01ContourInputI00.row20.drop 400).take 16)=true ∧
 ((RHBatch01ContourInputR00.row20.drop 400).take 16).length=16 := by decide +kernel
theorem checked20_26 : check v 10656
 ((RHBatch01ContourInputR00.row20.drop 416).take 16) ((RHBatch01ContourInputI00.row20.drop 416).take 16)=true ∧
 ((RHBatch01ContourInputR00.row20.drop 416).take 16).length=16 := by decide +kernel
theorem checked20_27 : check v 10672
 ((RHBatch01ContourInputR00.row20.drop 432).take 16) ((RHBatch01ContourInputI00.row20.drop 432).take 16)=true ∧
 ((RHBatch01ContourInputR00.row20.drop 432).take 16).length=16 := by decide +kernel
theorem checked20_28 : check v 10688
 ((RHBatch01ContourInputR00.row20.drop 448).take 16) ((RHBatch01ContourInputI00.row20.drop 448).take 16)=true ∧
 ((RHBatch01ContourInputR00.row20.drop 448).take 16).length=16 := by decide +kernel
theorem checked20_29 : check v 10704
 ((RHBatch01ContourInputR00.row20.drop 464).take 16) ((RHBatch01ContourInputI00.row20.drop 464).take 16)=true ∧
 ((RHBatch01ContourInputR00.row20.drop 464).take 16).length=16 := by decide +kernel
theorem checked20_30 : check v 10720
 ((RHBatch01ContourInputR00.row20.drop 480).take 16) ((RHBatch01ContourInputI00.row20.drop 480).take 16)=true ∧
 ((RHBatch01ContourInputR00.row20.drop 480).take 16).length=16 := by decide +kernel
theorem checked20_31 : check v 10736
 ((RHBatch01ContourInputR00.row20.drop 496).take 16) ((RHBatch01ContourInputI00.row20.drop 496).take 16)=true ∧
 ((RHBatch01ContourInputR00.row20.drop 496).take 16).length=16 := by decide +kernel
theorem checked21_00 : check v 10752
 ((RHBatch01ContourInputR00.row21.drop 0).take 16) ((RHBatch01ContourInputI00.row21.drop 0).take 16)=true ∧
 ((RHBatch01ContourInputR00.row21.drop 0).take 16).length=16 := by decide +kernel
theorem checked21_01 : check v 10768
 ((RHBatch01ContourInputR00.row21.drop 16).take 16) ((RHBatch01ContourInputI00.row21.drop 16).take 16)=true ∧
 ((RHBatch01ContourInputR00.row21.drop 16).take 16).length=16 := by decide +kernel
theorem checked21_02 : check v 10784
 ((RHBatch01ContourInputR00.row21.drop 32).take 16) ((RHBatch01ContourInputI00.row21.drop 32).take 16)=true ∧
 ((RHBatch01ContourInputR00.row21.drop 32).take 16).length=16 := by decide +kernel
theorem checked21_03 : check v 10800
 ((RHBatch01ContourInputR00.row21.drop 48).take 16) ((RHBatch01ContourInputI00.row21.drop 48).take 16)=true ∧
 ((RHBatch01ContourInputR00.row21.drop 48).take 16).length=16 := by decide +kernel
theorem checked21_04 : check v 10816
 ((RHBatch01ContourInputR00.row21.drop 64).take 16) ((RHBatch01ContourInputI00.row21.drop 64).take 16)=true ∧
 ((RHBatch01ContourInputR00.row21.drop 64).take 16).length=16 := by decide +kernel
theorem checked21_05 : check v 10832
 ((RHBatch01ContourInputR00.row21.drop 80).take 16) ((RHBatch01ContourInputI00.row21.drop 80).take 16)=true ∧
 ((RHBatch01ContourInputR00.row21.drop 80).take 16).length=16 := by decide +kernel
theorem checked21_06 : check v 10848
 ((RHBatch01ContourInputR00.row21.drop 96).take 16) ((RHBatch01ContourInputI00.row21.drop 96).take 16)=true ∧
 ((RHBatch01ContourInputR00.row21.drop 96).take 16).length=16 := by decide +kernel
theorem checked21_07 : check v 10864
 ((RHBatch01ContourInputR00.row21.drop 112).take 16) ((RHBatch01ContourInputI00.row21.drop 112).take 16)=true ∧
 ((RHBatch01ContourInputR00.row21.drop 112).take 16).length=16 := by decide +kernel
theorem checked21_08 : check v 10880
 ((RHBatch01ContourInputR00.row21.drop 128).take 16) ((RHBatch01ContourInputI00.row21.drop 128).take 16)=true ∧
 ((RHBatch01ContourInputR00.row21.drop 128).take 16).length=16 := by decide +kernel
theorem checked21_09 : check v 10896
 ((RHBatch01ContourInputR00.row21.drop 144).take 16) ((RHBatch01ContourInputI00.row21.drop 144).take 16)=true ∧
 ((RHBatch01ContourInputR00.row21.drop 144).take 16).length=16 := by decide +kernel
theorem checked21_10 : check v 10912
 ((RHBatch01ContourInputR00.row21.drop 160).take 16) ((RHBatch01ContourInputI00.row21.drop 160).take 16)=true ∧
 ((RHBatch01ContourInputR00.row21.drop 160).take 16).length=16 := by decide +kernel
theorem checked21_11 : check v 10928
 ((RHBatch01ContourInputR00.row21.drop 176).take 16) ((RHBatch01ContourInputI00.row21.drop 176).take 16)=true ∧
 ((RHBatch01ContourInputR00.row21.drop 176).take 16).length=16 := by decide +kernel
theorem checked21_12 : check v 10944
 ((RHBatch01ContourInputR00.row21.drop 192).take 16) ((RHBatch01ContourInputI00.row21.drop 192).take 16)=true ∧
 ((RHBatch01ContourInputR00.row21.drop 192).take 16).length=16 := by decide +kernel
theorem checked21_13 : check v 10960
 ((RHBatch01ContourInputR00.row21.drop 208).take 16) ((RHBatch01ContourInputI00.row21.drop 208).take 16)=true ∧
 ((RHBatch01ContourInputR00.row21.drop 208).take 16).length=16 := by decide +kernel
theorem checked21_14 : check v 10976
 ((RHBatch01ContourInputR00.row21.drop 224).take 16) ((RHBatch01ContourInputI00.row21.drop 224).take 16)=true ∧
 ((RHBatch01ContourInputR00.row21.drop 224).take 16).length=16 := by decide +kernel
theorem checked21_15 : check v 10992
 ((RHBatch01ContourInputR00.row21.drop 240).take 16) ((RHBatch01ContourInputI00.row21.drop 240).take 16)=true ∧
 ((RHBatch01ContourInputR00.row21.drop 240).take 16).length=16 := by decide +kernel
theorem checked21_16 : check v 11008
 ((RHBatch01ContourInputR00.row21.drop 256).take 16) ((RHBatch01ContourInputI00.row21.drop 256).take 16)=true ∧
 ((RHBatch01ContourInputR00.row21.drop 256).take 16).length=16 := by decide +kernel
theorem checked21_17 : check v 11024
 ((RHBatch01ContourInputR00.row21.drop 272).take 16) ((RHBatch01ContourInputI00.row21.drop 272).take 16)=true ∧
 ((RHBatch01ContourInputR00.row21.drop 272).take 16).length=16 := by decide +kernel
theorem checked21_18 : check v 11040
 ((RHBatch01ContourInputR00.row21.drop 288).take 16) ((RHBatch01ContourInputI00.row21.drop 288).take 16)=true ∧
 ((RHBatch01ContourInputR00.row21.drop 288).take 16).length=16 := by decide +kernel
theorem checked21_19 : check v 11056
 ((RHBatch01ContourInputR00.row21.drop 304).take 16) ((RHBatch01ContourInputI00.row21.drop 304).take 16)=true ∧
 ((RHBatch01ContourInputR00.row21.drop 304).take 16).length=16 := by decide +kernel
theorem checked21_20 : check v 11072
 ((RHBatch01ContourInputR00.row21.drop 320).take 16) ((RHBatch01ContourInputI00.row21.drop 320).take 16)=true ∧
 ((RHBatch01ContourInputR00.row21.drop 320).take 16).length=16 := by decide +kernel
theorem checked21_21 : check v 11088
 ((RHBatch01ContourInputR00.row21.drop 336).take 16) ((RHBatch01ContourInputI00.row21.drop 336).take 16)=true ∧
 ((RHBatch01ContourInputR00.row21.drop 336).take 16).length=16 := by decide +kernel
theorem checked21_22 : check v 11104
 ((RHBatch01ContourInputR00.row21.drop 352).take 16) ((RHBatch01ContourInputI00.row21.drop 352).take 16)=true ∧
 ((RHBatch01ContourInputR00.row21.drop 352).take 16).length=16 := by decide +kernel
theorem checked21_23 : check v 11120
 ((RHBatch01ContourInputR00.row21.drop 368).take 16) ((RHBatch01ContourInputI00.row21.drop 368).take 16)=true ∧
 ((RHBatch01ContourInputR00.row21.drop 368).take 16).length=16 := by decide +kernel
theorem checked21_24 : check v 11136
 ((RHBatch01ContourInputR00.row21.drop 384).take 16) ((RHBatch01ContourInputI00.row21.drop 384).take 16)=true ∧
 ((RHBatch01ContourInputR00.row21.drop 384).take 16).length=16 := by decide +kernel
theorem checked21_25 : check v 11152
 ((RHBatch01ContourInputR00.row21.drop 400).take 16) ((RHBatch01ContourInputI00.row21.drop 400).take 16)=true ∧
 ((RHBatch01ContourInputR00.row21.drop 400).take 16).length=16 := by decide +kernel
theorem checked21_26 : check v 11168
 ((RHBatch01ContourInputR00.row21.drop 416).take 16) ((RHBatch01ContourInputI00.row21.drop 416).take 16)=true ∧
 ((RHBatch01ContourInputR00.row21.drop 416).take 16).length=16 := by decide +kernel
theorem checked21_27 : check v 11184
 ((RHBatch01ContourInputR00.row21.drop 432).take 16) ((RHBatch01ContourInputI00.row21.drop 432).take 16)=true ∧
 ((RHBatch01ContourInputR00.row21.drop 432).take 16).length=16 := by decide +kernel
theorem checked21_28 : check v 11200
 ((RHBatch01ContourInputR00.row21.drop 448).take 16) ((RHBatch01ContourInputI00.row21.drop 448).take 16)=true ∧
 ((RHBatch01ContourInputR00.row21.drop 448).take 16).length=16 := by decide +kernel
theorem checked21_29 : check v 11216
 ((RHBatch01ContourInputR00.row21.drop 464).take 16) ((RHBatch01ContourInputI00.row21.drop 464).take 16)=true ∧
 ((RHBatch01ContourInputR00.row21.drop 464).take 16).length=16 := by decide +kernel
theorem checked21_30 : check v 11232
 ((RHBatch01ContourInputR00.row21.drop 480).take 16) ((RHBatch01ContourInputI00.row21.drop 480).take 16)=true ∧
 ((RHBatch01ContourInputR00.row21.drop 480).take 16).length=16 := by decide +kernel
theorem checked21_31 : check v 11248
 ((RHBatch01ContourInputR00.row21.drop 496).take 16) ((RHBatch01ContourInputI00.row21.drop 496).take 16)=true ∧
 ((RHBatch01ContourInputR00.row21.drop 496).take 16).length=16 := by decide +kernel
theorem checked22_00 : check v 11264
 ((RHBatch01ContourInputR00.row22.drop 0).take 16) ((RHBatch01ContourInputI00.row22.drop 0).take 16)=true ∧
 ((RHBatch01ContourInputR00.row22.drop 0).take 16).length=16 := by decide +kernel
theorem checked22_01 : check v 11280
 ((RHBatch01ContourInputR00.row22.drop 16).take 16) ((RHBatch01ContourInputI00.row22.drop 16).take 16)=true ∧
 ((RHBatch01ContourInputR00.row22.drop 16).take 16).length=16 := by decide +kernel
theorem checked22_02 : check v 11296
 ((RHBatch01ContourInputR00.row22.drop 32).take 16) ((RHBatch01ContourInputI00.row22.drop 32).take 16)=true ∧
 ((RHBatch01ContourInputR00.row22.drop 32).take 16).length=16 := by decide +kernel
theorem checked22_03 : check v 11312
 ((RHBatch01ContourInputR00.row22.drop 48).take 16) ((RHBatch01ContourInputI00.row22.drop 48).take 16)=true ∧
 ((RHBatch01ContourInputR00.row22.drop 48).take 16).length=16 := by decide +kernel
theorem checked22_04 : check v 11328
 ((RHBatch01ContourInputR00.row22.drop 64).take 16) ((RHBatch01ContourInputI00.row22.drop 64).take 16)=true ∧
 ((RHBatch01ContourInputR00.row22.drop 64).take 16).length=16 := by decide +kernel
theorem checked22_05 : check v 11344
 ((RHBatch01ContourInputR00.row22.drop 80).take 16) ((RHBatch01ContourInputI00.row22.drop 80).take 16)=true ∧
 ((RHBatch01ContourInputR00.row22.drop 80).take 16).length=16 := by decide +kernel
theorem checked22_06 : check v 11360
 ((RHBatch01ContourInputR00.row22.drop 96).take 16) ((RHBatch01ContourInputI00.row22.drop 96).take 16)=true ∧
 ((RHBatch01ContourInputR00.row22.drop 96).take 16).length=16 := by decide +kernel
theorem checked22_07 : check v 11376
 ((RHBatch01ContourInputR00.row22.drop 112).take 16) ((RHBatch01ContourInputI00.row22.drop 112).take 16)=true ∧
 ((RHBatch01ContourInputR00.row22.drop 112).take 16).length=16 := by decide +kernel
theorem checked22_08 : check v 11392
 ((RHBatch01ContourInputR00.row22.drop 128).take 16) ((RHBatch01ContourInputI00.row22.drop 128).take 16)=true ∧
 ((RHBatch01ContourInputR00.row22.drop 128).take 16).length=16 := by decide +kernel
theorem checked22_09 : check v 11408
 ((RHBatch01ContourInputR00.row22.drop 144).take 16) ((RHBatch01ContourInputI00.row22.drop 144).take 16)=true ∧
 ((RHBatch01ContourInputR00.row22.drop 144).take 16).length=16 := by decide +kernel
theorem checked22_10 : check v 11424
 ((RHBatch01ContourInputR00.row22.drop 160).take 16) ((RHBatch01ContourInputI00.row22.drop 160).take 16)=true ∧
 ((RHBatch01ContourInputR00.row22.drop 160).take 16).length=16 := by decide +kernel
theorem checked22_11 : check v 11440
 ((RHBatch01ContourInputR00.row22.drop 176).take 16) ((RHBatch01ContourInputI00.row22.drop 176).take 16)=true ∧
 ((RHBatch01ContourInputR00.row22.drop 176).take 16).length=16 := by decide +kernel
theorem checked22_12 : check v 11456
 ((RHBatch01ContourInputR00.row22.drop 192).take 16) ((RHBatch01ContourInputI00.row22.drop 192).take 16)=true ∧
 ((RHBatch01ContourInputR00.row22.drop 192).take 16).length=16 := by decide +kernel
theorem checked22_13 : check v 11472
 ((RHBatch01ContourInputR00.row22.drop 208).take 16) ((RHBatch01ContourInputI00.row22.drop 208).take 16)=true ∧
 ((RHBatch01ContourInputR00.row22.drop 208).take 16).length=16 := by decide +kernel
theorem checked22_14 : check v 11488
 ((RHBatch01ContourInputR00.row22.drop 224).take 16) ((RHBatch01ContourInputI00.row22.drop 224).take 16)=true ∧
 ((RHBatch01ContourInputR00.row22.drop 224).take 16).length=16 := by decide +kernel
theorem checked22_15 : check v 11504
 ((RHBatch01ContourInputR00.row22.drop 240).take 16) ((RHBatch01ContourInputI00.row22.drop 240).take 16)=true ∧
 ((RHBatch01ContourInputR00.row22.drop 240).take 16).length=16 := by decide +kernel
theorem checked22_16 : check v 11520
 ((RHBatch01ContourInputR00.row22.drop 256).take 16) ((RHBatch01ContourInputI00.row22.drop 256).take 16)=true ∧
 ((RHBatch01ContourInputR00.row22.drop 256).take 16).length=16 := by decide +kernel
theorem checked22_17 : check v 11536
 ((RHBatch01ContourInputR00.row22.drop 272).take 16) ((RHBatch01ContourInputI00.row22.drop 272).take 16)=true ∧
 ((RHBatch01ContourInputR00.row22.drop 272).take 16).length=16 := by decide +kernel
theorem checked22_18 : check v 11552
 ((RHBatch01ContourInputR00.row22.drop 288).take 16) ((RHBatch01ContourInputI00.row22.drop 288).take 16)=true ∧
 ((RHBatch01ContourInputR00.row22.drop 288).take 16).length=16 := by decide +kernel
theorem checked22_19 : check v 11568
 ((RHBatch01ContourInputR00.row22.drop 304).take 16) ((RHBatch01ContourInputI00.row22.drop 304).take 16)=true ∧
 ((RHBatch01ContourInputR00.row22.drop 304).take 16).length=16 := by decide +kernel
theorem checked22_20 : check v 11584
 ((RHBatch01ContourInputR00.row22.drop 320).take 16) ((RHBatch01ContourInputI00.row22.drop 320).take 16)=true ∧
 ((RHBatch01ContourInputR00.row22.drop 320).take 16).length=16 := by decide +kernel
theorem checked22_21 : check v 11600
 ((RHBatch01ContourInputR00.row22.drop 336).take 16) ((RHBatch01ContourInputI00.row22.drop 336).take 16)=true ∧
 ((RHBatch01ContourInputR00.row22.drop 336).take 16).length=16 := by decide +kernel
theorem checked22_22 : check v 11616
 ((RHBatch01ContourInputR00.row22.drop 352).take 16) ((RHBatch01ContourInputI00.row22.drop 352).take 16)=true ∧
 ((RHBatch01ContourInputR00.row22.drop 352).take 16).length=16 := by decide +kernel
theorem checked22_23 : check v 11632
 ((RHBatch01ContourInputR00.row22.drop 368).take 16) ((RHBatch01ContourInputI00.row22.drop 368).take 16)=true ∧
 ((RHBatch01ContourInputR00.row22.drop 368).take 16).length=16 := by decide +kernel
theorem checked22_24 : check v 11648
 ((RHBatch01ContourInputR00.row22.drop 384).take 16) ((RHBatch01ContourInputI00.row22.drop 384).take 16)=true ∧
 ((RHBatch01ContourInputR00.row22.drop 384).take 16).length=16 := by decide +kernel
theorem checked22_25 : check v 11664
 ((RHBatch01ContourInputR00.row22.drop 400).take 16) ((RHBatch01ContourInputI00.row22.drop 400).take 16)=true ∧
 ((RHBatch01ContourInputR00.row22.drop 400).take 16).length=16 := by decide +kernel
theorem checked22_26 : check v 11680
 ((RHBatch01ContourInputR00.row22.drop 416).take 16) ((RHBatch01ContourInputI00.row22.drop 416).take 16)=true ∧
 ((RHBatch01ContourInputR00.row22.drop 416).take 16).length=16 := by decide +kernel
theorem checked22_27 : check v 11696
 ((RHBatch01ContourInputR00.row22.drop 432).take 16) ((RHBatch01ContourInputI00.row22.drop 432).take 16)=true ∧
 ((RHBatch01ContourInputR00.row22.drop 432).take 16).length=16 := by decide +kernel
theorem checked22_28 : check v 11712
 ((RHBatch01ContourInputR00.row22.drop 448).take 16) ((RHBatch01ContourInputI00.row22.drop 448).take 16)=true ∧
 ((RHBatch01ContourInputR00.row22.drop 448).take 16).length=16 := by decide +kernel
theorem checked22_29 : check v 11728
 ((RHBatch01ContourInputR00.row22.drop 464).take 16) ((RHBatch01ContourInputI00.row22.drop 464).take 16)=true ∧
 ((RHBatch01ContourInputR00.row22.drop 464).take 16).length=16 := by decide +kernel
theorem checked22_30 : check v 11744
 ((RHBatch01ContourInputR00.row22.drop 480).take 16) ((RHBatch01ContourInputI00.row22.drop 480).take 16)=true ∧
 ((RHBatch01ContourInputR00.row22.drop 480).take 16).length=16 := by decide +kernel
theorem checked22_31 : check v 11760
 ((RHBatch01ContourInputR00.row22.drop 496).take 16) ((RHBatch01ContourInputI00.row22.drop 496).take 16)=true ∧
 ((RHBatch01ContourInputR00.row22.drop 496).take 16).length=16 := by decide +kernel
theorem checked23_00 : check v 11776
 ((RHBatch01ContourInputR00.row23.drop 0).take 16) ((RHBatch01ContourInputI00.row23.drop 0).take 16)=true ∧
 ((RHBatch01ContourInputR00.row23.drop 0).take 16).length=16 := by decide +kernel
theorem checked23_01 : check v 11792
 ((RHBatch01ContourInputR00.row23.drop 16).take 16) ((RHBatch01ContourInputI00.row23.drop 16).take 16)=true ∧
 ((RHBatch01ContourInputR00.row23.drop 16).take 16).length=16 := by decide +kernel
theorem checked23_02 : check v 11808
 ((RHBatch01ContourInputR00.row23.drop 32).take 16) ((RHBatch01ContourInputI00.row23.drop 32).take 16)=true ∧
 ((RHBatch01ContourInputR00.row23.drop 32).take 16).length=16 := by decide +kernel
theorem checked23_03 : check v 11824
 ((RHBatch01ContourInputR00.row23.drop 48).take 16) ((RHBatch01ContourInputI00.row23.drop 48).take 16)=true ∧
 ((RHBatch01ContourInputR00.row23.drop 48).take 16).length=16 := by decide +kernel
theorem checked23_04 : check v 11840
 ((RHBatch01ContourInputR00.row23.drop 64).take 16) ((RHBatch01ContourInputI00.row23.drop 64).take 16)=true ∧
 ((RHBatch01ContourInputR00.row23.drop 64).take 16).length=16 := by decide +kernel
theorem checked23_05 : check v 11856
 ((RHBatch01ContourInputR00.row23.drop 80).take 16) ((RHBatch01ContourInputI00.row23.drop 80).take 16)=true ∧
 ((RHBatch01ContourInputR00.row23.drop 80).take 16).length=16 := by decide +kernel
theorem checked23_06 : check v 11872
 ((RHBatch01ContourInputR00.row23.drop 96).take 16) ((RHBatch01ContourInputI00.row23.drop 96).take 16)=true ∧
 ((RHBatch01ContourInputR00.row23.drop 96).take 16).length=16 := by decide +kernel
theorem checked23_07 : check v 11888
 ((RHBatch01ContourInputR00.row23.drop 112).take 16) ((RHBatch01ContourInputI00.row23.drop 112).take 16)=true ∧
 ((RHBatch01ContourInputR00.row23.drop 112).take 16).length=16 := by decide +kernel
theorem checked23_08 : check v 11904
 ((RHBatch01ContourInputR00.row23.drop 128).take 16) ((RHBatch01ContourInputI00.row23.drop 128).take 16)=true ∧
 ((RHBatch01ContourInputR00.row23.drop 128).take 16).length=16 := by decide +kernel
theorem checked23_09 : check v 11920
 ((RHBatch01ContourInputR00.row23.drop 144).take 16) ((RHBatch01ContourInputI00.row23.drop 144).take 16)=true ∧
 ((RHBatch01ContourInputR00.row23.drop 144).take 16).length=16 := by decide +kernel
theorem checked23_10 : check v 11936
 ((RHBatch01ContourInputR00.row23.drop 160).take 16) ((RHBatch01ContourInputI00.row23.drop 160).take 16)=true ∧
 ((RHBatch01ContourInputR00.row23.drop 160).take 16).length=16 := by decide +kernel
theorem checked23_11 : check v 11952
 ((RHBatch01ContourInputR00.row23.drop 176).take 16) ((RHBatch01ContourInputI00.row23.drop 176).take 16)=true ∧
 ((RHBatch01ContourInputR00.row23.drop 176).take 16).length=16 := by decide +kernel
theorem checked23_12 : check v 11968
 ((RHBatch01ContourInputR00.row23.drop 192).take 16) ((RHBatch01ContourInputI00.row23.drop 192).take 16)=true ∧
 ((RHBatch01ContourInputR00.row23.drop 192).take 16).length=16 := by decide +kernel
theorem checked23_13 : check v 11984
 ((RHBatch01ContourInputR00.row23.drop 208).take 16) ((RHBatch01ContourInputI00.row23.drop 208).take 16)=true ∧
 ((RHBatch01ContourInputR00.row23.drop 208).take 16).length=16 := by decide +kernel
theorem checked23_14 : check v 12000
 ((RHBatch01ContourInputR00.row23.drop 224).take 16) ((RHBatch01ContourInputI00.row23.drop 224).take 16)=true ∧
 ((RHBatch01ContourInputR00.row23.drop 224).take 16).length=16 := by decide +kernel
theorem checked23_15 : check v 12016
 ((RHBatch01ContourInputR00.row23.drop 240).take 16) ((RHBatch01ContourInputI00.row23.drop 240).take 16)=true ∧
 ((RHBatch01ContourInputR00.row23.drop 240).take 16).length=16 := by decide +kernel
theorem checked23_16 : check v 12032
 ((RHBatch01ContourInputR00.row23.drop 256).take 16) ((RHBatch01ContourInputI00.row23.drop 256).take 16)=true ∧
 ((RHBatch01ContourInputR00.row23.drop 256).take 16).length=16 := by decide +kernel
theorem checked23_17 : check v 12048
 ((RHBatch01ContourInputR00.row23.drop 272).take 16) ((RHBatch01ContourInputI00.row23.drop 272).take 16)=true ∧
 ((RHBatch01ContourInputR00.row23.drop 272).take 16).length=16 := by decide +kernel
theorem checked23_18 : check v 12064
 ((RHBatch01ContourInputR00.row23.drop 288).take 16) ((RHBatch01ContourInputI00.row23.drop 288).take 16)=true ∧
 ((RHBatch01ContourInputR00.row23.drop 288).take 16).length=16 := by decide +kernel
theorem checked23_19 : check v 12080
 ((RHBatch01ContourInputR00.row23.drop 304).take 16) ((RHBatch01ContourInputI00.row23.drop 304).take 16)=true ∧
 ((RHBatch01ContourInputR00.row23.drop 304).take 16).length=16 := by decide +kernel
theorem checked23_20 : check v 12096
 ((RHBatch01ContourInputR00.row23.drop 320).take 16) ((RHBatch01ContourInputI00.row23.drop 320).take 16)=true ∧
 ((RHBatch01ContourInputR00.row23.drop 320).take 16).length=16 := by decide +kernel
theorem checked23_21 : check v 12112
 ((RHBatch01ContourInputR00.row23.drop 336).take 16) ((RHBatch01ContourInputI00.row23.drop 336).take 16)=true ∧
 ((RHBatch01ContourInputR00.row23.drop 336).take 16).length=16 := by decide +kernel
theorem checked23_22 : check v 12128
 ((RHBatch01ContourInputR00.row23.drop 352).take 16) ((RHBatch01ContourInputI00.row23.drop 352).take 16)=true ∧
 ((RHBatch01ContourInputR00.row23.drop 352).take 16).length=16 := by decide +kernel
theorem checked23_23 : check v 12144
 ((RHBatch01ContourInputR00.row23.drop 368).take 16) ((RHBatch01ContourInputI00.row23.drop 368).take 16)=true ∧
 ((RHBatch01ContourInputR00.row23.drop 368).take 16).length=16 := by decide +kernel
theorem checked23_24 : check v 12160
 ((RHBatch01ContourInputR00.row23.drop 384).take 16) ((RHBatch01ContourInputI00.row23.drop 384).take 16)=true ∧
 ((RHBatch01ContourInputR00.row23.drop 384).take 16).length=16 := by decide +kernel
theorem checked23_25 : check v 12176
 ((RHBatch01ContourInputR00.row23.drop 400).take 16) ((RHBatch01ContourInputI00.row23.drop 400).take 16)=true ∧
 ((RHBatch01ContourInputR00.row23.drop 400).take 16).length=16 := by decide +kernel
theorem checked23_26 : check v 12192
 ((RHBatch01ContourInputR00.row23.drop 416).take 16) ((RHBatch01ContourInputI00.row23.drop 416).take 16)=true ∧
 ((RHBatch01ContourInputR00.row23.drop 416).take 16).length=16 := by decide +kernel
theorem checked23_27 : check v 12208
 ((RHBatch01ContourInputR00.row23.drop 432).take 16) ((RHBatch01ContourInputI00.row23.drop 432).take 16)=true ∧
 ((RHBatch01ContourInputR00.row23.drop 432).take 16).length=16 := by decide +kernel
theorem checked23_28 : check v 12224
 ((RHBatch01ContourInputR00.row23.drop 448).take 16) ((RHBatch01ContourInputI00.row23.drop 448).take 16)=true ∧
 ((RHBatch01ContourInputR00.row23.drop 448).take 16).length=16 := by decide +kernel
theorem checked23_29 : check v 12240
 ((RHBatch01ContourInputR00.row23.drop 464).take 16) ((RHBatch01ContourInputI00.row23.drop 464).take 16)=true ∧
 ((RHBatch01ContourInputR00.row23.drop 464).take 16).length=16 := by decide +kernel
theorem checked23_30 : check v 12256
 ((RHBatch01ContourInputR00.row23.drop 480).take 16) ((RHBatch01ContourInputI00.row23.drop 480).take 16)=true ∧
 ((RHBatch01ContourInputR00.row23.drop 480).take 16).length=16 := by decide +kernel
theorem checked23_31 : check v 12272
 ((RHBatch01ContourInputR00.row23.drop 496).take 16) ((RHBatch01ContourInputI00.row23.drop 496).take 16)=true ∧
 ((RHBatch01ContourInputR00.row23.drop 496).take 16).length=16 := by decide +kernel
theorem checked24_00 : check v 12288
 ((RHBatch01ContourInputR00.row24.drop 0).take 16) ((RHBatch01ContourInputI00.row24.drop 0).take 16)=true ∧
 ((RHBatch01ContourInputR00.row24.drop 0).take 16).length=16 := by decide +kernel
theorem checked24_01 : check v 12304
 ((RHBatch01ContourInputR00.row24.drop 16).take 16) ((RHBatch01ContourInputI00.row24.drop 16).take 16)=true ∧
 ((RHBatch01ContourInputR00.row24.drop 16).take 16).length=16 := by decide +kernel
theorem checked24_02 : check v 12320
 ((RHBatch01ContourInputR00.row24.drop 32).take 16) ((RHBatch01ContourInputI00.row24.drop 32).take 16)=true ∧
 ((RHBatch01ContourInputR00.row24.drop 32).take 16).length=16 := by decide +kernel
theorem checked24_03 : check v 12336
 ((RHBatch01ContourInputR00.row24.drop 48).take 16) ((RHBatch01ContourInputI00.row24.drop 48).take 16)=true ∧
 ((RHBatch01ContourInputR00.row24.drop 48).take 16).length=16 := by decide +kernel
theorem checked24_04 : check v 12352
 ((RHBatch01ContourInputR00.row24.drop 64).take 16) ((RHBatch01ContourInputI00.row24.drop 64).take 16)=true ∧
 ((RHBatch01ContourInputR00.row24.drop 64).take 16).length=16 := by decide +kernel
theorem checked24_05 : check v 12368
 ((RHBatch01ContourInputR00.row24.drop 80).take 16) ((RHBatch01ContourInputI00.row24.drop 80).take 16)=true ∧
 ((RHBatch01ContourInputR00.row24.drop 80).take 16).length=16 := by decide +kernel
theorem checked24_06 : check v 12384
 ((RHBatch01ContourInputR00.row24.drop 96).take 16) ((RHBatch01ContourInputI00.row24.drop 96).take 16)=true ∧
 ((RHBatch01ContourInputR00.row24.drop 96).take 16).length=16 := by decide +kernel
theorem checked24_07 : check v 12400
 ((RHBatch01ContourInputR00.row24.drop 112).take 16) ((RHBatch01ContourInputI00.row24.drop 112).take 16)=true ∧
 ((RHBatch01ContourInputR00.row24.drop 112).take 16).length=16 := by decide +kernel
theorem checked24_08 : check v 12416
 ((RHBatch01ContourInputR00.row24.drop 128).take 16) ((RHBatch01ContourInputI00.row24.drop 128).take 16)=true ∧
 ((RHBatch01ContourInputR00.row24.drop 128).take 16).length=16 := by decide +kernel
theorem checked24_09 : check v 12432
 ((RHBatch01ContourInputR00.row24.drop 144).take 16) ((RHBatch01ContourInputI00.row24.drop 144).take 16)=true ∧
 ((RHBatch01ContourInputR00.row24.drop 144).take 16).length=16 := by decide +kernel
theorem checked24_10 : check v 12448
 ((RHBatch01ContourInputR00.row24.drop 160).take 16) ((RHBatch01ContourInputI00.row24.drop 160).take 16)=true ∧
 ((RHBatch01ContourInputR00.row24.drop 160).take 16).length=16 := by decide +kernel
theorem checked24_11 : check v 12464
 ((RHBatch01ContourInputR00.row24.drop 176).take 16) ((RHBatch01ContourInputI00.row24.drop 176).take 16)=true ∧
 ((RHBatch01ContourInputR00.row24.drop 176).take 16).length=16 := by decide +kernel
theorem checked24_12 : check v 12480
 ((RHBatch01ContourInputR00.row24.drop 192).take 16) ((RHBatch01ContourInputI00.row24.drop 192).take 16)=true ∧
 ((RHBatch01ContourInputR00.row24.drop 192).take 16).length=16 := by decide +kernel
theorem checked24_13 : check v 12496
 ((RHBatch01ContourInputR00.row24.drop 208).take 16) ((RHBatch01ContourInputI00.row24.drop 208).take 16)=true ∧
 ((RHBatch01ContourInputR00.row24.drop 208).take 16).length=16 := by decide +kernel
theorem checked24_14 : check v 12512
 ((RHBatch01ContourInputR00.row24.drop 224).take 16) ((RHBatch01ContourInputI00.row24.drop 224).take 16)=true ∧
 ((RHBatch01ContourInputR00.row24.drop 224).take 16).length=16 := by decide +kernel
theorem checked24_15 : check v 12528
 ((RHBatch01ContourInputR00.row24.drop 240).take 16) ((RHBatch01ContourInputI00.row24.drop 240).take 16)=true ∧
 ((RHBatch01ContourInputR00.row24.drop 240).take 16).length=16 := by decide +kernel
theorem checked24_16 : check v 12544
 ((RHBatch01ContourInputR00.row24.drop 256).take 16) ((RHBatch01ContourInputI00.row24.drop 256).take 16)=true ∧
 ((RHBatch01ContourInputR00.row24.drop 256).take 16).length=16 := by decide +kernel
theorem checked24_17 : check v 12560
 ((RHBatch01ContourInputR00.row24.drop 272).take 16) ((RHBatch01ContourInputI00.row24.drop 272).take 16)=true ∧
 ((RHBatch01ContourInputR00.row24.drop 272).take 16).length=16 := by decide +kernel
theorem checked24_18 : check v 12576
 ((RHBatch01ContourInputR00.row24.drop 288).take 16) ((RHBatch01ContourInputI00.row24.drop 288).take 16)=true ∧
 ((RHBatch01ContourInputR00.row24.drop 288).take 16).length=16 := by decide +kernel
theorem checked24_19 : check v 12592
 ((RHBatch01ContourInputR00.row24.drop 304).take 16) ((RHBatch01ContourInputI00.row24.drop 304).take 16)=true ∧
 ((RHBatch01ContourInputR00.row24.drop 304).take 16).length=16 := by decide +kernel
theorem checked24_20 : check v 12608
 ((RHBatch01ContourInputR00.row24.drop 320).take 16) ((RHBatch01ContourInputI00.row24.drop 320).take 16)=true ∧
 ((RHBatch01ContourInputR00.row24.drop 320).take 16).length=16 := by decide +kernel
theorem checked24_21 : check v 12624
 ((RHBatch01ContourInputR00.row24.drop 336).take 16) ((RHBatch01ContourInputI00.row24.drop 336).take 16)=true ∧
 ((RHBatch01ContourInputR00.row24.drop 336).take 16).length=16 := by decide +kernel
theorem checked24_22 : check v 12640
 ((RHBatch01ContourInputR00.row24.drop 352).take 16) ((RHBatch01ContourInputI00.row24.drop 352).take 16)=true ∧
 ((RHBatch01ContourInputR00.row24.drop 352).take 16).length=16 := by decide +kernel
theorem checked24_23 : check v 12656
 ((RHBatch01ContourInputR00.row24.drop 368).take 16) ((RHBatch01ContourInputI00.row24.drop 368).take 16)=true ∧
 ((RHBatch01ContourInputR00.row24.drop 368).take 16).length=16 := by decide +kernel
theorem checked24_24 : check v 12672
 ((RHBatch01ContourInputR00.row24.drop 384).take 16) ((RHBatch01ContourInputI00.row24.drop 384).take 16)=true ∧
 ((RHBatch01ContourInputR00.row24.drop 384).take 16).length=16 := by decide +kernel
theorem checked24_25 : check v 12688
 ((RHBatch01ContourInputR00.row24.drop 400).take 16) ((RHBatch01ContourInputI00.row24.drop 400).take 16)=true ∧
 ((RHBatch01ContourInputR00.row24.drop 400).take 16).length=16 := by decide +kernel
theorem checked24_26 : check v 12704
 ((RHBatch01ContourInputR00.row24.drop 416).take 16) ((RHBatch01ContourInputI00.row24.drop 416).take 16)=true ∧
 ((RHBatch01ContourInputR00.row24.drop 416).take 16).length=16 := by decide +kernel
theorem checked24_27 : check v 12720
 ((RHBatch01ContourInputR00.row24.drop 432).take 16) ((RHBatch01ContourInputI00.row24.drop 432).take 16)=true ∧
 ((RHBatch01ContourInputR00.row24.drop 432).take 16).length=16 := by decide +kernel
theorem checked24_28 : check v 12736
 ((RHBatch01ContourInputR00.row24.drop 448).take 16) ((RHBatch01ContourInputI00.row24.drop 448).take 16)=true ∧
 ((RHBatch01ContourInputR00.row24.drop 448).take 16).length=16 := by decide +kernel
theorem checked24_29 : check v 12752
 ((RHBatch01ContourInputR00.row24.drop 464).take 16) ((RHBatch01ContourInputI00.row24.drop 464).take 16)=true ∧
 ((RHBatch01ContourInputR00.row24.drop 464).take 16).length=16 := by decide +kernel
theorem checked24_30 : check v 12768
 ((RHBatch01ContourInputR00.row24.drop 480).take 16) ((RHBatch01ContourInputI00.row24.drop 480).take 16)=true ∧
 ((RHBatch01ContourInputR00.row24.drop 480).take 16).length=16 := by decide +kernel
theorem checked24_31 : check v 12784
 ((RHBatch01ContourInputR00.row24.drop 496).take 16) ((RHBatch01ContourInputI00.row24.drop 496).take 16)=true ∧
 ((RHBatch01ContourInputR00.row24.drop 496).take 16).length=16 := by decide +kernel
theorem checked25_00 : check v 12800
 ((RHBatch01ContourInputR00.row25.drop 0).take 16) ((RHBatch01ContourInputI00.row25.drop 0).take 16)=true ∧
 ((RHBatch01ContourInputR00.row25.drop 0).take 16).length=16 := by decide +kernel
theorem checked25_01 : check v 12816
 ((RHBatch01ContourInputR00.row25.drop 16).take 16) ((RHBatch01ContourInputI00.row25.drop 16).take 16)=true ∧
 ((RHBatch01ContourInputR00.row25.drop 16).take 16).length=16 := by decide +kernel
theorem checked25_02 : check v 12832
 ((RHBatch01ContourInputR00.row25.drop 32).take 16) ((RHBatch01ContourInputI00.row25.drop 32).take 16)=true ∧
 ((RHBatch01ContourInputR00.row25.drop 32).take 16).length=16 := by decide +kernel
theorem checked25_03 : check v 12848
 ((RHBatch01ContourInputR00.row25.drop 48).take 16) ((RHBatch01ContourInputI00.row25.drop 48).take 16)=true ∧
 ((RHBatch01ContourInputR00.row25.drop 48).take 16).length=16 := by decide +kernel
theorem checked25_04 : check v 12864
 ((RHBatch01ContourInputR00.row25.drop 64).take 16) ((RHBatch01ContourInputI00.row25.drop 64).take 16)=true ∧
 ((RHBatch01ContourInputR00.row25.drop 64).take 16).length=16 := by decide +kernel
theorem checked25_05 : check v 12880
 ((RHBatch01ContourInputR00.row25.drop 80).take 16) ((RHBatch01ContourInputI00.row25.drop 80).take 16)=true ∧
 ((RHBatch01ContourInputR00.row25.drop 80).take 16).length=16 := by decide +kernel
theorem checked25_06 : check v 12896
 ((RHBatch01ContourInputR00.row25.drop 96).take 16) ((RHBatch01ContourInputI00.row25.drop 96).take 16)=true ∧
 ((RHBatch01ContourInputR00.row25.drop 96).take 16).length=16 := by decide +kernel
theorem checked25_07 : check v 12912
 ((RHBatch01ContourInputR00.row25.drop 112).take 16) ((RHBatch01ContourInputI00.row25.drop 112).take 16)=true ∧
 ((RHBatch01ContourInputR00.row25.drop 112).take 16).length=16 := by decide +kernel
theorem checked25_08 : check v 12928
 ((RHBatch01ContourInputR00.row25.drop 128).take 16) ((RHBatch01ContourInputI00.row25.drop 128).take 16)=true ∧
 ((RHBatch01ContourInputR00.row25.drop 128).take 16).length=16 := by decide +kernel
theorem checked25_09 : check v 12944
 ((RHBatch01ContourInputR00.row25.drop 144).take 16) ((RHBatch01ContourInputI00.row25.drop 144).take 16)=true ∧
 ((RHBatch01ContourInputR00.row25.drop 144).take 16).length=16 := by decide +kernel
theorem checked25_10 : check v 12960
 ((RHBatch01ContourInputR00.row25.drop 160).take 16) ((RHBatch01ContourInputI00.row25.drop 160).take 16)=true ∧
 ((RHBatch01ContourInputR00.row25.drop 160).take 16).length=16 := by decide +kernel
theorem checked25_11 : check v 12976
 ((RHBatch01ContourInputR00.row25.drop 176).take 16) ((RHBatch01ContourInputI00.row25.drop 176).take 16)=true ∧
 ((RHBatch01ContourInputR00.row25.drop 176).take 16).length=16 := by decide +kernel
theorem checked25_12 : check v 12992
 ((RHBatch01ContourInputR00.row25.drop 192).take 16) ((RHBatch01ContourInputI00.row25.drop 192).take 16)=true ∧
 ((RHBatch01ContourInputR00.row25.drop 192).take 16).length=16 := by decide +kernel
theorem checked25_13 : check v 13008
 ((RHBatch01ContourInputR00.row25.drop 208).take 16) ((RHBatch01ContourInputI00.row25.drop 208).take 16)=true ∧
 ((RHBatch01ContourInputR00.row25.drop 208).take 16).length=16 := by decide +kernel
theorem checked25_14 : check v 13024
 ((RHBatch01ContourInputR00.row25.drop 224).take 16) ((RHBatch01ContourInputI00.row25.drop 224).take 16)=true ∧
 ((RHBatch01ContourInputR00.row25.drop 224).take 16).length=16 := by decide +kernel
theorem checked25_15 : check v 13040
 ((RHBatch01ContourInputR00.row25.drop 240).take 16) ((RHBatch01ContourInputI00.row25.drop 240).take 16)=true ∧
 ((RHBatch01ContourInputR00.row25.drop 240).take 16).length=16 := by decide +kernel
theorem checked25_16 : check v 13056
 ((RHBatch01ContourInputR00.row25.drop 256).take 16) ((RHBatch01ContourInputI00.row25.drop 256).take 16)=true ∧
 ((RHBatch01ContourInputR00.row25.drop 256).take 16).length=16 := by decide +kernel
theorem checked25_17 : check v 13072
 ((RHBatch01ContourInputR00.row25.drop 272).take 16) ((RHBatch01ContourInputI00.row25.drop 272).take 16)=true ∧
 ((RHBatch01ContourInputR00.row25.drop 272).take 16).length=16 := by decide +kernel
theorem checked25_18 : check v 13088
 ((RHBatch01ContourInputR00.row25.drop 288).take 16) ((RHBatch01ContourInputI00.row25.drop 288).take 16)=true ∧
 ((RHBatch01ContourInputR00.row25.drop 288).take 16).length=16 := by decide +kernel
theorem checked25_19 : check v 13104
 ((RHBatch01ContourInputR00.row25.drop 304).take 16) ((RHBatch01ContourInputI00.row25.drop 304).take 16)=true ∧
 ((RHBatch01ContourInputR00.row25.drop 304).take 16).length=16 := by decide +kernel
theorem checked25_20 : check v 13120
 ((RHBatch01ContourInputR00.row25.drop 320).take 16) ((RHBatch01ContourInputI00.row25.drop 320).take 16)=true ∧
 ((RHBatch01ContourInputR00.row25.drop 320).take 16).length=16 := by decide +kernel
theorem checked25_21 : check v 13136
 ((RHBatch01ContourInputR00.row25.drop 336).take 16) ((RHBatch01ContourInputI00.row25.drop 336).take 16)=true ∧
 ((RHBatch01ContourInputR00.row25.drop 336).take 16).length=16 := by decide +kernel
theorem checked25_22 : check v 13152
 ((RHBatch01ContourInputR00.row25.drop 352).take 16) ((RHBatch01ContourInputI00.row25.drop 352).take 16)=true ∧
 ((RHBatch01ContourInputR00.row25.drop 352).take 16).length=16 := by decide +kernel
theorem checked25_23 : check v 13168
 ((RHBatch01ContourInputR00.row25.drop 368).take 16) ((RHBatch01ContourInputI00.row25.drop 368).take 16)=true ∧
 ((RHBatch01ContourInputR00.row25.drop 368).take 16).length=16 := by decide +kernel
theorem checked25_24 : check v 13184
 ((RHBatch01ContourInputR00.row25.drop 384).take 16) ((RHBatch01ContourInputI00.row25.drop 384).take 16)=true ∧
 ((RHBatch01ContourInputR00.row25.drop 384).take 16).length=16 := by decide +kernel
theorem checked25_25 : check v 13200
 ((RHBatch01ContourInputR00.row25.drop 400).take 16) ((RHBatch01ContourInputI00.row25.drop 400).take 16)=true ∧
 ((RHBatch01ContourInputR00.row25.drop 400).take 16).length=16 := by decide +kernel
theorem checked25_26 : check v 13216
 ((RHBatch01ContourInputR00.row25.drop 416).take 16) ((RHBatch01ContourInputI00.row25.drop 416).take 16)=true ∧
 ((RHBatch01ContourInputR00.row25.drop 416).take 16).length=16 := by decide +kernel
theorem checked25_27 : check v 13232
 ((RHBatch01ContourInputR00.row25.drop 432).take 16) ((RHBatch01ContourInputI00.row25.drop 432).take 16)=true ∧
 ((RHBatch01ContourInputR00.row25.drop 432).take 16).length=16 := by decide +kernel
theorem checked25_28 : check v 13248
 ((RHBatch01ContourInputR00.row25.drop 448).take 16) ((RHBatch01ContourInputI00.row25.drop 448).take 16)=true ∧
 ((RHBatch01ContourInputR00.row25.drop 448).take 16).length=16 := by decide +kernel
theorem checked25_29 : check v 13264
 ((RHBatch01ContourInputR00.row25.drop 464).take 16) ((RHBatch01ContourInputI00.row25.drop 464).take 16)=true ∧
 ((RHBatch01ContourInputR00.row25.drop 464).take 16).length=16 := by decide +kernel
theorem checked25_30 : check v 13280
 ((RHBatch01ContourInputR00.row25.drop 480).take 16) ((RHBatch01ContourInputI00.row25.drop 480).take 16)=true ∧
 ((RHBatch01ContourInputR00.row25.drop 480).take 16).length=16 := by decide +kernel
theorem checked25_31 : check v 13296
 ((RHBatch01ContourInputR00.row25.drop 496).take 16) ((RHBatch01ContourInputI00.row25.drop 496).take 16)=true ∧
 ((RHBatch01ContourInputR00.row25.drop 496).take 16).length=16 := by decide +kernel
theorem checked26_00 : check v 13312
 ((RHBatch01ContourInputR00.row26.drop 0).take 16) ((RHBatch01ContourInputI00.row26.drop 0).take 16)=true ∧
 ((RHBatch01ContourInputR00.row26.drop 0).take 16).length=16 := by decide +kernel
theorem checked26_01 : check v 13328
 ((RHBatch01ContourInputR00.row26.drop 16).take 16) ((RHBatch01ContourInputI00.row26.drop 16).take 16)=true ∧
 ((RHBatch01ContourInputR00.row26.drop 16).take 16).length=16 := by decide +kernel
theorem checked26_02 : check v 13344
 ((RHBatch01ContourInputR00.row26.drop 32).take 16) ((RHBatch01ContourInputI00.row26.drop 32).take 16)=true ∧
 ((RHBatch01ContourInputR00.row26.drop 32).take 16).length=16 := by decide +kernel
theorem checked26_03 : check v 13360
 ((RHBatch01ContourInputR00.row26.drop 48).take 16) ((RHBatch01ContourInputI00.row26.drop 48).take 16)=true ∧
 ((RHBatch01ContourInputR00.row26.drop 48).take 16).length=16 := by decide +kernel
theorem checked26_04 : check v 13376
 ((RHBatch01ContourInputR00.row26.drop 64).take 16) ((RHBatch01ContourInputI00.row26.drop 64).take 16)=true ∧
 ((RHBatch01ContourInputR00.row26.drop 64).take 16).length=16 := by decide +kernel
theorem checked26_05 : check v 13392
 ((RHBatch01ContourInputR00.row26.drop 80).take 16) ((RHBatch01ContourInputI00.row26.drop 80).take 16)=true ∧
 ((RHBatch01ContourInputR00.row26.drop 80).take 16).length=16 := by decide +kernel
theorem checked26_06 : check v 13408
 ((RHBatch01ContourInputR00.row26.drop 96).take 16) ((RHBatch01ContourInputI00.row26.drop 96).take 16)=true ∧
 ((RHBatch01ContourInputR00.row26.drop 96).take 16).length=16 := by decide +kernel
theorem checked26_07 : check v 13424
 ((RHBatch01ContourInputR00.row26.drop 112).take 16) ((RHBatch01ContourInputI00.row26.drop 112).take 16)=true ∧
 ((RHBatch01ContourInputR00.row26.drop 112).take 16).length=16 := by decide +kernel
theorem checked26_08 : check v 13440
 ((RHBatch01ContourInputR00.row26.drop 128).take 16) ((RHBatch01ContourInputI00.row26.drop 128).take 16)=true ∧
 ((RHBatch01ContourInputR00.row26.drop 128).take 16).length=16 := by decide +kernel
theorem checked26_09 : check v 13456
 ((RHBatch01ContourInputR00.row26.drop 144).take 16) ((RHBatch01ContourInputI00.row26.drop 144).take 16)=true ∧
 ((RHBatch01ContourInputR00.row26.drop 144).take 16).length=16 := by decide +kernel
theorem checked26_10 : check v 13472
 ((RHBatch01ContourInputR00.row26.drop 160).take 16) ((RHBatch01ContourInputI00.row26.drop 160).take 16)=true ∧
 ((RHBatch01ContourInputR00.row26.drop 160).take 16).length=16 := by decide +kernel
theorem checked26_11 : check v 13488
 ((RHBatch01ContourInputR00.row26.drop 176).take 16) ((RHBatch01ContourInputI00.row26.drop 176).take 16)=true ∧
 ((RHBatch01ContourInputR00.row26.drop 176).take 16).length=16 := by decide +kernel
theorem checked26_12 : check v 13504
 ((RHBatch01ContourInputR00.row26.drop 192).take 16) ((RHBatch01ContourInputI00.row26.drop 192).take 16)=true ∧
 ((RHBatch01ContourInputR00.row26.drop 192).take 16).length=16 := by decide +kernel
theorem checked26_13 : check v 13520
 ((RHBatch01ContourInputR00.row26.drop 208).take 16) ((RHBatch01ContourInputI00.row26.drop 208).take 16)=true ∧
 ((RHBatch01ContourInputR00.row26.drop 208).take 16).length=16 := by decide +kernel
theorem checked26_14 : check v 13536
 ((RHBatch01ContourInputR00.row26.drop 224).take 16) ((RHBatch01ContourInputI00.row26.drop 224).take 16)=true ∧
 ((RHBatch01ContourInputR00.row26.drop 224).take 16).length=16 := by decide +kernel
theorem checked26_15 : check v 13552
 ((RHBatch01ContourInputR00.row26.drop 240).take 16) ((RHBatch01ContourInputI00.row26.drop 240).take 16)=true ∧
 ((RHBatch01ContourInputR00.row26.drop 240).take 16).length=16 := by decide +kernel
theorem checked26_16 : check v 13568
 ((RHBatch01ContourInputR00.row26.drop 256).take 16) ((RHBatch01ContourInputI00.row26.drop 256).take 16)=true ∧
 ((RHBatch01ContourInputR00.row26.drop 256).take 16).length=16 := by decide +kernel
theorem checked26_17 : check v 13584
 ((RHBatch01ContourInputR00.row26.drop 272).take 16) ((RHBatch01ContourInputI00.row26.drop 272).take 16)=true ∧
 ((RHBatch01ContourInputR00.row26.drop 272).take 16).length=16 := by decide +kernel
theorem checked26_18 : check v 13600
 ((RHBatch01ContourInputR00.row26.drop 288).take 16) ((RHBatch01ContourInputI00.row26.drop 288).take 16)=true ∧
 ((RHBatch01ContourInputR00.row26.drop 288).take 16).length=16 := by decide +kernel
theorem checked26_19 : check v 13616
 ((RHBatch01ContourInputR00.row26.drop 304).take 16) ((RHBatch01ContourInputI00.row26.drop 304).take 16)=true ∧
 ((RHBatch01ContourInputR00.row26.drop 304).take 16).length=16 := by decide +kernel
theorem checked26_20 : check v 13632
 ((RHBatch01ContourInputR00.row26.drop 320).take 16) ((RHBatch01ContourInputI00.row26.drop 320).take 16)=true ∧
 ((RHBatch01ContourInputR00.row26.drop 320).take 16).length=16 := by decide +kernel
theorem checked26_21 : check v 13648
 ((RHBatch01ContourInputR00.row26.drop 336).take 16) ((RHBatch01ContourInputI00.row26.drop 336).take 16)=true ∧
 ((RHBatch01ContourInputR00.row26.drop 336).take 16).length=16 := by decide +kernel
theorem checked26_22 : check v 13664
 ((RHBatch01ContourInputR00.row26.drop 352).take 16) ((RHBatch01ContourInputI00.row26.drop 352).take 16)=true ∧
 ((RHBatch01ContourInputR00.row26.drop 352).take 16).length=16 := by decide +kernel
theorem checked26_23 : check v 13680
 ((RHBatch01ContourInputR00.row26.drop 368).take 16) ((RHBatch01ContourInputI00.row26.drop 368).take 16)=true ∧
 ((RHBatch01ContourInputR00.row26.drop 368).take 16).length=16 := by decide +kernel
theorem checked26_24 : check v 13696
 ((RHBatch01ContourInputR00.row26.drop 384).take 16) ((RHBatch01ContourInputI00.row26.drop 384).take 16)=true ∧
 ((RHBatch01ContourInputR00.row26.drop 384).take 16).length=16 := by decide +kernel
theorem checked26_25 : check v 13712
 ((RHBatch01ContourInputR00.row26.drop 400).take 16) ((RHBatch01ContourInputI00.row26.drop 400).take 16)=true ∧
 ((RHBatch01ContourInputR00.row26.drop 400).take 16).length=16 := by decide +kernel
theorem checked26_26 : check v 13728
 ((RHBatch01ContourInputR00.row26.drop 416).take 16) ((RHBatch01ContourInputI00.row26.drop 416).take 16)=true ∧
 ((RHBatch01ContourInputR00.row26.drop 416).take 16).length=16 := by decide +kernel
theorem checked26_27 : check v 13744
 ((RHBatch01ContourInputR00.row26.drop 432).take 16) ((RHBatch01ContourInputI00.row26.drop 432).take 16)=true ∧
 ((RHBatch01ContourInputR00.row26.drop 432).take 16).length=16 := by decide +kernel
theorem checked26_28 : check v 13760
 ((RHBatch01ContourInputR00.row26.drop 448).take 16) ((RHBatch01ContourInputI00.row26.drop 448).take 16)=true ∧
 ((RHBatch01ContourInputR00.row26.drop 448).take 16).length=16 := by decide +kernel
theorem checked26_29 : check v 13776
 ((RHBatch01ContourInputR00.row26.drop 464).take 16) ((RHBatch01ContourInputI00.row26.drop 464).take 16)=true ∧
 ((RHBatch01ContourInputR00.row26.drop 464).take 16).length=16 := by decide +kernel
theorem checked26_30 : check v 13792
 ((RHBatch01ContourInputR00.row26.drop 480).take 16) ((RHBatch01ContourInputI00.row26.drop 480).take 16)=true ∧
 ((RHBatch01ContourInputR00.row26.drop 480).take 16).length=16 := by decide +kernel
theorem checked26_31 : check v 13808
 ((RHBatch01ContourInputR00.row26.drop 496).take 16) ((RHBatch01ContourInputI00.row26.drop 496).take 16)=true ∧
 ((RHBatch01ContourInputR00.row26.drop 496).take 16).length=16 := by decide +kernel
theorem checked27_00 : check v 13824
 ((RHBatch01ContourInputR00.row27.drop 0).take 16) ((RHBatch01ContourInputI00.row27.drop 0).take 16)=true ∧
 ((RHBatch01ContourInputR00.row27.drop 0).take 16).length=16 := by decide +kernel
theorem checked27_01 : check v 13840
 ((RHBatch01ContourInputR00.row27.drop 16).take 16) ((RHBatch01ContourInputI00.row27.drop 16).take 16)=true ∧
 ((RHBatch01ContourInputR00.row27.drop 16).take 16).length=16 := by decide +kernel
theorem checked27_02 : check v 13856
 ((RHBatch01ContourInputR00.row27.drop 32).take 16) ((RHBatch01ContourInputI00.row27.drop 32).take 16)=true ∧
 ((RHBatch01ContourInputR00.row27.drop 32).take 16).length=16 := by decide +kernel
theorem checked27_03 : check v 13872
 ((RHBatch01ContourInputR00.row27.drop 48).take 16) ((RHBatch01ContourInputI00.row27.drop 48).take 16)=true ∧
 ((RHBatch01ContourInputR00.row27.drop 48).take 16).length=16 := by decide +kernel
theorem checked27_04 : check v 13888
 ((RHBatch01ContourInputR00.row27.drop 64).take 16) ((RHBatch01ContourInputI00.row27.drop 64).take 16)=true ∧
 ((RHBatch01ContourInputR00.row27.drop 64).take 16).length=16 := by decide +kernel
theorem checked27_05 : check v 13904
 ((RHBatch01ContourInputR00.row27.drop 80).take 16) ((RHBatch01ContourInputI00.row27.drop 80).take 16)=true ∧
 ((RHBatch01ContourInputR00.row27.drop 80).take 16).length=16 := by decide +kernel
theorem checked27_06 : check v 13920
 ((RHBatch01ContourInputR00.row27.drop 96).take 16) ((RHBatch01ContourInputI00.row27.drop 96).take 16)=true ∧
 ((RHBatch01ContourInputR00.row27.drop 96).take 16).length=16 := by decide +kernel
theorem checked27_07 : check v 13936
 ((RHBatch01ContourInputR00.row27.drop 112).take 16) ((RHBatch01ContourInputI00.row27.drop 112).take 16)=true ∧
 ((RHBatch01ContourInputR00.row27.drop 112).take 16).length=16 := by decide +kernel
theorem checked27_08 : check v 13952
 ((RHBatch01ContourInputR00.row27.drop 128).take 16) ((RHBatch01ContourInputI00.row27.drop 128).take 16)=true ∧
 ((RHBatch01ContourInputR00.row27.drop 128).take 16).length=16 := by decide +kernel
theorem checked27_09 : check v 13968
 ((RHBatch01ContourInputR00.row27.drop 144).take 16) ((RHBatch01ContourInputI00.row27.drop 144).take 16)=true ∧
 ((RHBatch01ContourInputR00.row27.drop 144).take 16).length=16 := by decide +kernel
theorem checked27_10 : check v 13984
 ((RHBatch01ContourInputR00.row27.drop 160).take 16) ((RHBatch01ContourInputI00.row27.drop 160).take 16)=true ∧
 ((RHBatch01ContourInputR00.row27.drop 160).take 16).length=16 := by decide +kernel
theorem checked27_11 : check v 14000
 ((RHBatch01ContourInputR00.row27.drop 176).take 16) ((RHBatch01ContourInputI00.row27.drop 176).take 16)=true ∧
 ((RHBatch01ContourInputR00.row27.drop 176).take 16).length=16 := by decide +kernel
theorem checked27_12 : check v 14016
 ((RHBatch01ContourInputR00.row27.drop 192).take 16) ((RHBatch01ContourInputI00.row27.drop 192).take 16)=true ∧
 ((RHBatch01ContourInputR00.row27.drop 192).take 16).length=16 := by decide +kernel
theorem checked27_13 : check v 14032
 ((RHBatch01ContourInputR00.row27.drop 208).take 16) ((RHBatch01ContourInputI00.row27.drop 208).take 16)=true ∧
 ((RHBatch01ContourInputR00.row27.drop 208).take 16).length=16 := by decide +kernel
theorem checked27_14 : check v 14048
 ((RHBatch01ContourInputR00.row27.drop 224).take 16) ((RHBatch01ContourInputI00.row27.drop 224).take 16)=true ∧
 ((RHBatch01ContourInputR00.row27.drop 224).take 16).length=16 := by decide +kernel
theorem checked27_15 : check v 14064
 ((RHBatch01ContourInputR00.row27.drop 240).take 16) ((RHBatch01ContourInputI00.row27.drop 240).take 16)=true ∧
 ((RHBatch01ContourInputR00.row27.drop 240).take 16).length=16 := by decide +kernel
theorem checked27_16 : check v 14080
 ((RHBatch01ContourInputR00.row27.drop 256).take 16) ((RHBatch01ContourInputI00.row27.drop 256).take 16)=true ∧
 ((RHBatch01ContourInputR00.row27.drop 256).take 16).length=16 := by decide +kernel
theorem checked27_17 : check v 14096
 ((RHBatch01ContourInputR00.row27.drop 272).take 16) ((RHBatch01ContourInputI00.row27.drop 272).take 16)=true ∧
 ((RHBatch01ContourInputR00.row27.drop 272).take 16).length=16 := by decide +kernel
theorem checked27_18 : check v 14112
 ((RHBatch01ContourInputR00.row27.drop 288).take 16) ((RHBatch01ContourInputI00.row27.drop 288).take 16)=true ∧
 ((RHBatch01ContourInputR00.row27.drop 288).take 16).length=16 := by decide +kernel
theorem checked27_19 : check v 14128
 ((RHBatch01ContourInputR00.row27.drop 304).take 16) ((RHBatch01ContourInputI00.row27.drop 304).take 16)=true ∧
 ((RHBatch01ContourInputR00.row27.drop 304).take 16).length=16 := by decide +kernel
theorem checked27_20 : check v 14144
 ((RHBatch01ContourInputR00.row27.drop 320).take 16) ((RHBatch01ContourInputI00.row27.drop 320).take 16)=true ∧
 ((RHBatch01ContourInputR00.row27.drop 320).take 16).length=16 := by decide +kernel
theorem checked27_21 : check v 14160
 ((RHBatch01ContourInputR00.row27.drop 336).take 16) ((RHBatch01ContourInputI00.row27.drop 336).take 16)=true ∧
 ((RHBatch01ContourInputR00.row27.drop 336).take 16).length=16 := by decide +kernel
theorem checked27_22 : check v 14176
 ((RHBatch01ContourInputR00.row27.drop 352).take 16) ((RHBatch01ContourInputI00.row27.drop 352).take 16)=true ∧
 ((RHBatch01ContourInputR00.row27.drop 352).take 16).length=16 := by decide +kernel
theorem checked27_23 : check v 14192
 ((RHBatch01ContourInputR00.row27.drop 368).take 16) ((RHBatch01ContourInputI00.row27.drop 368).take 16)=true ∧
 ((RHBatch01ContourInputR00.row27.drop 368).take 16).length=16 := by decide +kernel
theorem checked27_24 : check v 14208
 ((RHBatch01ContourInputR00.row27.drop 384).take 16) ((RHBatch01ContourInputI00.row27.drop 384).take 16)=true ∧
 ((RHBatch01ContourInputR00.row27.drop 384).take 16).length=16 := by decide +kernel
theorem checked27_25 : check v 14224
 ((RHBatch01ContourInputR00.row27.drop 400).take 16) ((RHBatch01ContourInputI00.row27.drop 400).take 16)=true ∧
 ((RHBatch01ContourInputR00.row27.drop 400).take 16).length=16 := by decide +kernel
theorem checked27_26 : check v 14240
 ((RHBatch01ContourInputR00.row27.drop 416).take 16) ((RHBatch01ContourInputI00.row27.drop 416).take 16)=true ∧
 ((RHBatch01ContourInputR00.row27.drop 416).take 16).length=16 := by decide +kernel
theorem checked27_27 : check v 14256
 ((RHBatch01ContourInputR00.row27.drop 432).take 16) ((RHBatch01ContourInputI00.row27.drop 432).take 16)=true ∧
 ((RHBatch01ContourInputR00.row27.drop 432).take 16).length=16 := by decide +kernel
theorem checked27_28 : check v 14272
 ((RHBatch01ContourInputR00.row27.drop 448).take 16) ((RHBatch01ContourInputI00.row27.drop 448).take 16)=true ∧
 ((RHBatch01ContourInputR00.row27.drop 448).take 16).length=16 := by decide +kernel
theorem checked27_29 : check v 14288
 ((RHBatch01ContourInputR00.row27.drop 464).take 16) ((RHBatch01ContourInputI00.row27.drop 464).take 16)=true ∧
 ((RHBatch01ContourInputR00.row27.drop 464).take 16).length=16 := by decide +kernel
theorem checked27_30 : check v 14304
 ((RHBatch01ContourInputR00.row27.drop 480).take 16) ((RHBatch01ContourInputI00.row27.drop 480).take 16)=true ∧
 ((RHBatch01ContourInputR00.row27.drop 480).take 16).length=16 := by decide +kernel
theorem checked27_31 : check v 14320
 ((RHBatch01ContourInputR00.row27.drop 496).take 16) ((RHBatch01ContourInputI00.row27.drop 496).take 16)=true ∧
 ((RHBatch01ContourInputR00.row27.drop 496).take 16).length=16 := by decide +kernel
theorem checked28_00 : check v 14336
 ((RHBatch01ContourInputR00.row28.drop 0).take 16) ((RHBatch01ContourInputI00.row28.drop 0).take 16)=true ∧
 ((RHBatch01ContourInputR00.row28.drop 0).take 16).length=16 := by decide +kernel
theorem checked28_01 : check v 14352
 ((RHBatch01ContourInputR00.row28.drop 16).take 16) ((RHBatch01ContourInputI00.row28.drop 16).take 16)=true ∧
 ((RHBatch01ContourInputR00.row28.drop 16).take 16).length=16 := by decide +kernel
theorem checked28_02 : check v 14368
 ((RHBatch01ContourInputR00.row28.drop 32).take 16) ((RHBatch01ContourInputI00.row28.drop 32).take 16)=true ∧
 ((RHBatch01ContourInputR00.row28.drop 32).take 16).length=16 := by decide +kernel
theorem checked28_03 : check v 14384
 ((RHBatch01ContourInputR00.row28.drop 48).take 16) ((RHBatch01ContourInputI00.row28.drop 48).take 16)=true ∧
 ((RHBatch01ContourInputR00.row28.drop 48).take 16).length=16 := by decide +kernel
theorem checked28_04 : check v 14400
 ((RHBatch01ContourInputR00.row28.drop 64).take 16) ((RHBatch01ContourInputI00.row28.drop 64).take 16)=true ∧
 ((RHBatch01ContourInputR00.row28.drop 64).take 16).length=16 := by decide +kernel
theorem checked28_05 : check v 14416
 ((RHBatch01ContourInputR00.row28.drop 80).take 16) ((RHBatch01ContourInputI00.row28.drop 80).take 16)=true ∧
 ((RHBatch01ContourInputR00.row28.drop 80).take 16).length=16 := by decide +kernel
theorem checked28_06 : check v 14432
 ((RHBatch01ContourInputR00.row28.drop 96).take 16) ((RHBatch01ContourInputI00.row28.drop 96).take 16)=true ∧
 ((RHBatch01ContourInputR00.row28.drop 96).take 16).length=16 := by decide +kernel
theorem checked28_07 : check v 14448
 ((RHBatch01ContourInputR00.row28.drop 112).take 16) ((RHBatch01ContourInputI00.row28.drop 112).take 16)=true ∧
 ((RHBatch01ContourInputR00.row28.drop 112).take 16).length=16 := by decide +kernel
theorem checked28_08 : check v 14464
 ((RHBatch01ContourInputR00.row28.drop 128).take 16) ((RHBatch01ContourInputI00.row28.drop 128).take 16)=true ∧
 ((RHBatch01ContourInputR00.row28.drop 128).take 16).length=16 := by decide +kernel
theorem checked28_09 : check v 14480
 ((RHBatch01ContourInputR00.row28.drop 144).take 16) ((RHBatch01ContourInputI00.row28.drop 144).take 16)=true ∧
 ((RHBatch01ContourInputR00.row28.drop 144).take 16).length=16 := by decide +kernel
theorem checked28_10 : check v 14496
 ((RHBatch01ContourInputR00.row28.drop 160).take 16) ((RHBatch01ContourInputI00.row28.drop 160).take 16)=true ∧
 ((RHBatch01ContourInputR00.row28.drop 160).take 16).length=16 := by decide +kernel
theorem checked28_11 : check v 14512
 ((RHBatch01ContourInputR00.row28.drop 176).take 16) ((RHBatch01ContourInputI00.row28.drop 176).take 16)=true ∧
 ((RHBatch01ContourInputR00.row28.drop 176).take 16).length=16 := by decide +kernel
theorem checked28_12 : check v 14528
 ((RHBatch01ContourInputR00.row28.drop 192).take 16) ((RHBatch01ContourInputI00.row28.drop 192).take 16)=true ∧
 ((RHBatch01ContourInputR00.row28.drop 192).take 16).length=16 := by decide +kernel
theorem checked28_13 : check v 14544
 ((RHBatch01ContourInputR00.row28.drop 208).take 16) ((RHBatch01ContourInputI00.row28.drop 208).take 16)=true ∧
 ((RHBatch01ContourInputR00.row28.drop 208).take 16).length=16 := by decide +kernel
theorem checked28_14 : check v 14560
 ((RHBatch01ContourInputR00.row28.drop 224).take 16) ((RHBatch01ContourInputI00.row28.drop 224).take 16)=true ∧
 ((RHBatch01ContourInputR00.row28.drop 224).take 16).length=16 := by decide +kernel
theorem checked28_15 : check v 14576
 ((RHBatch01ContourInputR00.row28.drop 240).take 16) ((RHBatch01ContourInputI00.row28.drop 240).take 16)=true ∧
 ((RHBatch01ContourInputR00.row28.drop 240).take 16).length=16 := by decide +kernel
theorem checked28_16 : check v 14592
 ((RHBatch01ContourInputR00.row28.drop 256).take 16) ((RHBatch01ContourInputI00.row28.drop 256).take 16)=true ∧
 ((RHBatch01ContourInputR00.row28.drop 256).take 16).length=16 := by decide +kernel
theorem checked28_17 : check v 14608
 ((RHBatch01ContourInputR00.row28.drop 272).take 16) ((RHBatch01ContourInputI00.row28.drop 272).take 16)=true ∧
 ((RHBatch01ContourInputR00.row28.drop 272).take 16).length=16 := by decide +kernel
theorem checked28_18 : check v 14624
 ((RHBatch01ContourInputR00.row28.drop 288).take 16) ((RHBatch01ContourInputI00.row28.drop 288).take 16)=true ∧
 ((RHBatch01ContourInputR00.row28.drop 288).take 16).length=16 := by decide +kernel
theorem checked28_19 : check v 14640
 ((RHBatch01ContourInputR00.row28.drop 304).take 16) ((RHBatch01ContourInputI00.row28.drop 304).take 16)=true ∧
 ((RHBatch01ContourInputR00.row28.drop 304).take 16).length=16 := by decide +kernel
theorem checked28_20 : check v 14656
 ((RHBatch01ContourInputR00.row28.drop 320).take 16) ((RHBatch01ContourInputI00.row28.drop 320).take 16)=true ∧
 ((RHBatch01ContourInputR00.row28.drop 320).take 16).length=16 := by decide +kernel
theorem checked28_21 : check v 14672
 ((RHBatch01ContourInputR00.row28.drop 336).take 16) ((RHBatch01ContourInputI00.row28.drop 336).take 16)=true ∧
 ((RHBatch01ContourInputR00.row28.drop 336).take 16).length=16 := by decide +kernel
theorem checked28_22 : check v 14688
 ((RHBatch01ContourInputR00.row28.drop 352).take 16) ((RHBatch01ContourInputI00.row28.drop 352).take 16)=true ∧
 ((RHBatch01ContourInputR00.row28.drop 352).take 16).length=16 := by decide +kernel
theorem checked28_23 : check v 14704
 ((RHBatch01ContourInputR00.row28.drop 368).take 16) ((RHBatch01ContourInputI00.row28.drop 368).take 16)=true ∧
 ((RHBatch01ContourInputR00.row28.drop 368).take 16).length=16 := by decide +kernel
theorem checked28_24 : check v 14720
 ((RHBatch01ContourInputR00.row28.drop 384).take 16) ((RHBatch01ContourInputI00.row28.drop 384).take 16)=true ∧
 ((RHBatch01ContourInputR00.row28.drop 384).take 16).length=16 := by decide +kernel
theorem checked28_25 : check v 14736
 ((RHBatch01ContourInputR00.row28.drop 400).take 16) ((RHBatch01ContourInputI00.row28.drop 400).take 16)=true ∧
 ((RHBatch01ContourInputR00.row28.drop 400).take 16).length=16 := by decide +kernel
theorem checked28_26 : check v 14752
 ((RHBatch01ContourInputR00.row28.drop 416).take 16) ((RHBatch01ContourInputI00.row28.drop 416).take 16)=true ∧
 ((RHBatch01ContourInputR00.row28.drop 416).take 16).length=16 := by decide +kernel
theorem checked28_27 : check v 14768
 ((RHBatch01ContourInputR00.row28.drop 432).take 16) ((RHBatch01ContourInputI00.row28.drop 432).take 16)=true ∧
 ((RHBatch01ContourInputR00.row28.drop 432).take 16).length=16 := by decide +kernel
theorem checked28_28 : check v 14784
 ((RHBatch01ContourInputR00.row28.drop 448).take 16) ((RHBatch01ContourInputI00.row28.drop 448).take 16)=true ∧
 ((RHBatch01ContourInputR00.row28.drop 448).take 16).length=16 := by decide +kernel
theorem checked28_29 : check v 14800
 ((RHBatch01ContourInputR00.row28.drop 464).take 16) ((RHBatch01ContourInputI00.row28.drop 464).take 16)=true ∧
 ((RHBatch01ContourInputR00.row28.drop 464).take 16).length=16 := by decide +kernel
theorem checked28_30 : check v 14816
 ((RHBatch01ContourInputR00.row28.drop 480).take 16) ((RHBatch01ContourInputI00.row28.drop 480).take 16)=true ∧
 ((RHBatch01ContourInputR00.row28.drop 480).take 16).length=16 := by decide +kernel
theorem checked28_31 : check v 14832
 ((RHBatch01ContourInputR00.row28.drop 496).take 16) ((RHBatch01ContourInputI00.row28.drop 496).take 16)=true ∧
 ((RHBatch01ContourInputR00.row28.drop 496).take 16).length=16 := by decide +kernel
theorem checked29_00 : check v 14848
 ((RHBatch01ContourInputR00.row29.drop 0).take 16) ((RHBatch01ContourInputI00.row29.drop 0).take 16)=true ∧
 ((RHBatch01ContourInputR00.row29.drop 0).take 16).length=16 := by decide +kernel
theorem checked29_01 : check v 14864
 ((RHBatch01ContourInputR00.row29.drop 16).take 16) ((RHBatch01ContourInputI00.row29.drop 16).take 16)=true ∧
 ((RHBatch01ContourInputR00.row29.drop 16).take 16).length=16 := by decide +kernel
theorem checked29_02 : check v 14880
 ((RHBatch01ContourInputR00.row29.drop 32).take 16) ((RHBatch01ContourInputI00.row29.drop 32).take 16)=true ∧
 ((RHBatch01ContourInputR00.row29.drop 32).take 16).length=16 := by decide +kernel
theorem checked29_03 : check v 14896
 ((RHBatch01ContourInputR00.row29.drop 48).take 16) ((RHBatch01ContourInputI00.row29.drop 48).take 16)=true ∧
 ((RHBatch01ContourInputR00.row29.drop 48).take 16).length=16 := by decide +kernel
theorem checked29_04 : check v 14912
 ((RHBatch01ContourInputR00.row29.drop 64).take 16) ((RHBatch01ContourInputI00.row29.drop 64).take 16)=true ∧
 ((RHBatch01ContourInputR00.row29.drop 64).take 16).length=16 := by decide +kernel
theorem checked29_05 : check v 14928
 ((RHBatch01ContourInputR00.row29.drop 80).take 16) ((RHBatch01ContourInputI00.row29.drop 80).take 16)=true ∧
 ((RHBatch01ContourInputR00.row29.drop 80).take 16).length=16 := by decide +kernel
theorem checked29_06 : check v 14944
 ((RHBatch01ContourInputR00.row29.drop 96).take 16) ((RHBatch01ContourInputI00.row29.drop 96).take 16)=true ∧
 ((RHBatch01ContourInputR00.row29.drop 96).take 16).length=16 := by decide +kernel
theorem checked29_07 : check v 14960
 ((RHBatch01ContourInputR00.row29.drop 112).take 16) ((RHBatch01ContourInputI00.row29.drop 112).take 16)=true ∧
 ((RHBatch01ContourInputR00.row29.drop 112).take 16).length=16 := by decide +kernel
theorem checked29_08 : check v 14976
 ((RHBatch01ContourInputR00.row29.drop 128).take 16) ((RHBatch01ContourInputI00.row29.drop 128).take 16)=true ∧
 ((RHBatch01ContourInputR00.row29.drop 128).take 16).length=16 := by decide +kernel
theorem checked29_09 : check v 14992
 ((RHBatch01ContourInputR00.row29.drop 144).take 16) ((RHBatch01ContourInputI00.row29.drop 144).take 16)=true ∧
 ((RHBatch01ContourInputR00.row29.drop 144).take 16).length=16 := by decide +kernel
theorem checked29_10 : check v 15008
 ((RHBatch01ContourInputR00.row29.drop 160).take 16) ((RHBatch01ContourInputI00.row29.drop 160).take 16)=true ∧
 ((RHBatch01ContourInputR00.row29.drop 160).take 16).length=16 := by decide +kernel
theorem checked29_11 : check v 15024
 ((RHBatch01ContourInputR00.row29.drop 176).take 16) ((RHBatch01ContourInputI00.row29.drop 176).take 16)=true ∧
 ((RHBatch01ContourInputR00.row29.drop 176).take 16).length=16 := by decide +kernel
theorem checked29_12 : check v 15040
 ((RHBatch01ContourInputR00.row29.drop 192).take 16) ((RHBatch01ContourInputI00.row29.drop 192).take 16)=true ∧
 ((RHBatch01ContourInputR00.row29.drop 192).take 16).length=16 := by decide +kernel
theorem checked29_13 : check v 15056
 ((RHBatch01ContourInputR00.row29.drop 208).take 16) ((RHBatch01ContourInputI00.row29.drop 208).take 16)=true ∧
 ((RHBatch01ContourInputR00.row29.drop 208).take 16).length=16 := by decide +kernel
theorem checked29_14 : check v 15072
 ((RHBatch01ContourInputR00.row29.drop 224).take 16) ((RHBatch01ContourInputI00.row29.drop 224).take 16)=true ∧
 ((RHBatch01ContourInputR00.row29.drop 224).take 16).length=16 := by decide +kernel
theorem checked29_15 : check v 15088
 ((RHBatch01ContourInputR00.row29.drop 240).take 16) ((RHBatch01ContourInputI00.row29.drop 240).take 16)=true ∧
 ((RHBatch01ContourInputR00.row29.drop 240).take 16).length=16 := by decide +kernel
theorem checked29_16 : check v 15104
 ((RHBatch01ContourInputR00.row29.drop 256).take 16) ((RHBatch01ContourInputI00.row29.drop 256).take 16)=true ∧
 ((RHBatch01ContourInputR00.row29.drop 256).take 16).length=16 := by decide +kernel
theorem checked29_17 : check v 15120
 ((RHBatch01ContourInputR00.row29.drop 272).take 16) ((RHBatch01ContourInputI00.row29.drop 272).take 16)=true ∧
 ((RHBatch01ContourInputR00.row29.drop 272).take 16).length=16 := by decide +kernel
theorem checked29_18 : check v 15136
 ((RHBatch01ContourInputR00.row29.drop 288).take 16) ((RHBatch01ContourInputI00.row29.drop 288).take 16)=true ∧
 ((RHBatch01ContourInputR00.row29.drop 288).take 16).length=16 := by decide +kernel
theorem checked29_19 : check v 15152
 ((RHBatch01ContourInputR00.row29.drop 304).take 16) ((RHBatch01ContourInputI00.row29.drop 304).take 16)=true ∧
 ((RHBatch01ContourInputR00.row29.drop 304).take 16).length=16 := by decide +kernel
theorem checked29_20 : check v 15168
 ((RHBatch01ContourInputR00.row29.drop 320).take 16) ((RHBatch01ContourInputI00.row29.drop 320).take 16)=true ∧
 ((RHBatch01ContourInputR00.row29.drop 320).take 16).length=16 := by decide +kernel
theorem checked29_21 : check v 15184
 ((RHBatch01ContourInputR00.row29.drop 336).take 16) ((RHBatch01ContourInputI00.row29.drop 336).take 16)=true ∧
 ((RHBatch01ContourInputR00.row29.drop 336).take 16).length=16 := by decide +kernel
theorem checked29_22 : check v 15200
 ((RHBatch01ContourInputR00.row29.drop 352).take 16) ((RHBatch01ContourInputI00.row29.drop 352).take 16)=true ∧
 ((RHBatch01ContourInputR00.row29.drop 352).take 16).length=16 := by decide +kernel
theorem checked29_23 : check v 15216
 ((RHBatch01ContourInputR00.row29.drop 368).take 16) ((RHBatch01ContourInputI00.row29.drop 368).take 16)=true ∧
 ((RHBatch01ContourInputR00.row29.drop 368).take 16).length=16 := by decide +kernel
theorem checked29_24 : check v 15232
 ((RHBatch01ContourInputR00.row29.drop 384).take 16) ((RHBatch01ContourInputI00.row29.drop 384).take 16)=true ∧
 ((RHBatch01ContourInputR00.row29.drop 384).take 16).length=16 := by decide +kernel
theorem checked29_25 : check v 15248
 ((RHBatch01ContourInputR00.row29.drop 400).take 16) ((RHBatch01ContourInputI00.row29.drop 400).take 16)=true ∧
 ((RHBatch01ContourInputR00.row29.drop 400).take 16).length=16 := by decide +kernel
theorem checked29_26 : check v 15264
 ((RHBatch01ContourInputR00.row29.drop 416).take 16) ((RHBatch01ContourInputI00.row29.drop 416).take 16)=true ∧
 ((RHBatch01ContourInputR00.row29.drop 416).take 16).length=16 := by decide +kernel
theorem checked29_27 : check v 15280
 ((RHBatch01ContourInputR00.row29.drop 432).take 16) ((RHBatch01ContourInputI00.row29.drop 432).take 16)=true ∧
 ((RHBatch01ContourInputR00.row29.drop 432).take 16).length=16 := by decide +kernel
theorem checked29_28 : check v 15296
 ((RHBatch01ContourInputR00.row29.drop 448).take 16) ((RHBatch01ContourInputI00.row29.drop 448).take 16)=true ∧
 ((RHBatch01ContourInputR00.row29.drop 448).take 16).length=16 := by decide +kernel
theorem checked29_29 : check v 15312
 ((RHBatch01ContourInputR00.row29.drop 464).take 16) ((RHBatch01ContourInputI00.row29.drop 464).take 16)=true ∧
 ((RHBatch01ContourInputR00.row29.drop 464).take 16).length=16 := by decide +kernel
theorem checked29_30 : check v 15328
 ((RHBatch01ContourInputR00.row29.drop 480).take 16) ((RHBatch01ContourInputI00.row29.drop 480).take 16)=true ∧
 ((RHBatch01ContourInputR00.row29.drop 480).take 16).length=16 := by decide +kernel
theorem checked29_31 : check v 15344
 ((RHBatch01ContourInputR00.row29.drop 496).take 16) ((RHBatch01ContourInputI00.row29.drop 496).take 16)=true ∧
 ((RHBatch01ContourInputR00.row29.drop 496).take 16).length=16 := by decide +kernel
theorem checked30_00 : check v 15360
 ((RHBatch01ContourInputR00.row30.drop 0).take 16) ((RHBatch01ContourInputI00.row30.drop 0).take 16)=true ∧
 ((RHBatch01ContourInputR00.row30.drop 0).take 16).length=16 := by decide +kernel
theorem checked30_01 : check v 15376
 ((RHBatch01ContourInputR00.row30.drop 16).take 16) ((RHBatch01ContourInputI00.row30.drop 16).take 16)=true ∧
 ((RHBatch01ContourInputR00.row30.drop 16).take 16).length=16 := by decide +kernel
theorem checked30_02 : check v 15392
 ((RHBatch01ContourInputR00.row30.drop 32).take 16) ((RHBatch01ContourInputI00.row30.drop 32).take 16)=true ∧
 ((RHBatch01ContourInputR00.row30.drop 32).take 16).length=16 := by decide +kernel
theorem checked30_03 : check v 15408
 ((RHBatch01ContourInputR00.row30.drop 48).take 16) ((RHBatch01ContourInputI00.row30.drop 48).take 16)=true ∧
 ((RHBatch01ContourInputR00.row30.drop 48).take 16).length=16 := by decide +kernel
theorem checked30_04 : check v 15424
 ((RHBatch01ContourInputR00.row30.drop 64).take 16) ((RHBatch01ContourInputI00.row30.drop 64).take 16)=true ∧
 ((RHBatch01ContourInputR00.row30.drop 64).take 16).length=16 := by decide +kernel
theorem checked30_05 : check v 15440
 ((RHBatch01ContourInputR00.row30.drop 80).take 16) ((RHBatch01ContourInputI00.row30.drop 80).take 16)=true ∧
 ((RHBatch01ContourInputR00.row30.drop 80).take 16).length=16 := by decide +kernel
theorem checked30_06 : check v 15456
 ((RHBatch01ContourInputR00.row30.drop 96).take 16) ((RHBatch01ContourInputI00.row30.drop 96).take 16)=true ∧
 ((RHBatch01ContourInputR00.row30.drop 96).take 16).length=16 := by decide +kernel
theorem checked30_07 : check v 15472
 ((RHBatch01ContourInputR00.row30.drop 112).take 16) ((RHBatch01ContourInputI00.row30.drop 112).take 16)=true ∧
 ((RHBatch01ContourInputR00.row30.drop 112).take 16).length=16 := by decide +kernel
theorem checked30_08 : check v 15488
 ((RHBatch01ContourInputR00.row30.drop 128).take 16) ((RHBatch01ContourInputI00.row30.drop 128).take 16)=true ∧
 ((RHBatch01ContourInputR00.row30.drop 128).take 16).length=16 := by decide +kernel
theorem checked30_09 : check v 15504
 ((RHBatch01ContourInputR00.row30.drop 144).take 16) ((RHBatch01ContourInputI00.row30.drop 144).take 16)=true ∧
 ((RHBatch01ContourInputR00.row30.drop 144).take 16).length=16 := by decide +kernel
theorem checked30_10 : check v 15520
 ((RHBatch01ContourInputR00.row30.drop 160).take 16) ((RHBatch01ContourInputI00.row30.drop 160).take 16)=true ∧
 ((RHBatch01ContourInputR00.row30.drop 160).take 16).length=16 := by decide +kernel
theorem checked30_11 : check v 15536
 ((RHBatch01ContourInputR00.row30.drop 176).take 16) ((RHBatch01ContourInputI00.row30.drop 176).take 16)=true ∧
 ((RHBatch01ContourInputR00.row30.drop 176).take 16).length=16 := by decide +kernel
theorem checked30_12 : check v 15552
 ((RHBatch01ContourInputR00.row30.drop 192).take 16) ((RHBatch01ContourInputI00.row30.drop 192).take 16)=true ∧
 ((RHBatch01ContourInputR00.row30.drop 192).take 16).length=16 := by decide +kernel
theorem checked30_13 : check v 15568
 ((RHBatch01ContourInputR00.row30.drop 208).take 16) ((RHBatch01ContourInputI00.row30.drop 208).take 16)=true ∧
 ((RHBatch01ContourInputR00.row30.drop 208).take 16).length=16 := by decide +kernel
theorem checked30_14 : check v 15584
 ((RHBatch01ContourInputR00.row30.drop 224).take 16) ((RHBatch01ContourInputI00.row30.drop 224).take 16)=true ∧
 ((RHBatch01ContourInputR00.row30.drop 224).take 16).length=16 := by decide +kernel
theorem checked30_15 : check v 15600
 ((RHBatch01ContourInputR00.row30.drop 240).take 16) ((RHBatch01ContourInputI00.row30.drop 240).take 16)=true ∧
 ((RHBatch01ContourInputR00.row30.drop 240).take 16).length=16 := by decide +kernel
theorem checked30_16 : check v 15616
 ((RHBatch01ContourInputR00.row30.drop 256).take 16) ((RHBatch01ContourInputI00.row30.drop 256).take 16)=true ∧
 ((RHBatch01ContourInputR00.row30.drop 256).take 16).length=16 := by decide +kernel
theorem checked30_17 : check v 15632
 ((RHBatch01ContourInputR00.row30.drop 272).take 16) ((RHBatch01ContourInputI00.row30.drop 272).take 16)=true ∧
 ((RHBatch01ContourInputR00.row30.drop 272).take 16).length=16 := by decide +kernel
theorem checked30_18 : check v 15648
 ((RHBatch01ContourInputR00.row30.drop 288).take 16) ((RHBatch01ContourInputI00.row30.drop 288).take 16)=true ∧
 ((RHBatch01ContourInputR00.row30.drop 288).take 16).length=16 := by decide +kernel
theorem checked30_19 : check v 15664
 ((RHBatch01ContourInputR00.row30.drop 304).take 16) ((RHBatch01ContourInputI00.row30.drop 304).take 16)=true ∧
 ((RHBatch01ContourInputR00.row30.drop 304).take 16).length=16 := by decide +kernel
theorem checked30_20 : check v 15680
 ((RHBatch01ContourInputR00.row30.drop 320).take 16) ((RHBatch01ContourInputI00.row30.drop 320).take 16)=true ∧
 ((RHBatch01ContourInputR00.row30.drop 320).take 16).length=16 := by decide +kernel
theorem checked30_21 : check v 15696
 ((RHBatch01ContourInputR00.row30.drop 336).take 16) ((RHBatch01ContourInputI00.row30.drop 336).take 16)=true ∧
 ((RHBatch01ContourInputR00.row30.drop 336).take 16).length=16 := by decide +kernel
theorem checked30_22 : check v 15712
 ((RHBatch01ContourInputR00.row30.drop 352).take 16) ((RHBatch01ContourInputI00.row30.drop 352).take 16)=true ∧
 ((RHBatch01ContourInputR00.row30.drop 352).take 16).length=16 := by decide +kernel
theorem checked30_23 : check v 15728
 ((RHBatch01ContourInputR00.row30.drop 368).take 16) ((RHBatch01ContourInputI00.row30.drop 368).take 16)=true ∧
 ((RHBatch01ContourInputR00.row30.drop 368).take 16).length=16 := by decide +kernel
theorem checked30_24 : check v 15744
 ((RHBatch01ContourInputR00.row30.drop 384).take 16) ((RHBatch01ContourInputI00.row30.drop 384).take 16)=true ∧
 ((RHBatch01ContourInputR00.row30.drop 384).take 16).length=16 := by decide +kernel
theorem checked30_25 : check v 15760
 ((RHBatch01ContourInputR00.row30.drop 400).take 16) ((RHBatch01ContourInputI00.row30.drop 400).take 16)=true ∧
 ((RHBatch01ContourInputR00.row30.drop 400).take 16).length=16 := by decide +kernel
theorem checked30_26 : check v 15776
 ((RHBatch01ContourInputR00.row30.drop 416).take 16) ((RHBatch01ContourInputI00.row30.drop 416).take 16)=true ∧
 ((RHBatch01ContourInputR00.row30.drop 416).take 16).length=16 := by decide +kernel
theorem checked30_27 : check v 15792
 ((RHBatch01ContourInputR00.row30.drop 432).take 16) ((RHBatch01ContourInputI00.row30.drop 432).take 16)=true ∧
 ((RHBatch01ContourInputR00.row30.drop 432).take 16).length=16 := by decide +kernel
theorem checked30_28 : check v 15808
 ((RHBatch01ContourInputR00.row30.drop 448).take 16) ((RHBatch01ContourInputI00.row30.drop 448).take 16)=true ∧
 ((RHBatch01ContourInputR00.row30.drop 448).take 16).length=16 := by decide +kernel
theorem checked30_29 : check v 15824
 ((RHBatch01ContourInputR00.row30.drop 464).take 16) ((RHBatch01ContourInputI00.row30.drop 464).take 16)=true ∧
 ((RHBatch01ContourInputR00.row30.drop 464).take 16).length=16 := by decide +kernel
theorem checked30_30 : check v 15840
 ((RHBatch01ContourInputR00.row30.drop 480).take 16) ((RHBatch01ContourInputI00.row30.drop 480).take 16)=true ∧
 ((RHBatch01ContourInputR00.row30.drop 480).take 16).length=16 := by decide +kernel
theorem checked30_31 : check v 15856
 ((RHBatch01ContourInputR00.row30.drop 496).take 16) ((RHBatch01ContourInputI00.row30.drop 496).take 16)=true ∧
 ((RHBatch01ContourInputR00.row30.drop 496).take 16).length=16 := by decide +kernel
theorem checked31_00 : check v 15872
 ((RHBatch01ContourInputR00.row31.drop 0).take 16) ((RHBatch01ContourInputI00.row31.drop 0).take 16)=true ∧
 ((RHBatch01ContourInputR00.row31.drop 0).take 16).length=16 := by decide +kernel
theorem checked31_01 : check v 15888
 ((RHBatch01ContourInputR00.row31.drop 16).take 16) ((RHBatch01ContourInputI00.row31.drop 16).take 16)=true ∧
 ((RHBatch01ContourInputR00.row31.drop 16).take 16).length=16 := by decide +kernel
theorem checked31_02 : check v 15904
 ((RHBatch01ContourInputR00.row31.drop 32).take 16) ((RHBatch01ContourInputI00.row31.drop 32).take 16)=true ∧
 ((RHBatch01ContourInputR00.row31.drop 32).take 16).length=16 := by decide +kernel
theorem checked31_03 : check v 15920
 ((RHBatch01ContourInputR00.row31.drop 48).take 16) ((RHBatch01ContourInputI00.row31.drop 48).take 16)=true ∧
 ((RHBatch01ContourInputR00.row31.drop 48).take 16).length=16 := by decide +kernel
theorem checked31_04 : check v 15936
 ((RHBatch01ContourInputR00.row31.drop 64).take 16) ((RHBatch01ContourInputI00.row31.drop 64).take 16)=true ∧
 ((RHBatch01ContourInputR00.row31.drop 64).take 16).length=16 := by decide +kernel
theorem checked31_05 : check v 15952
 ((RHBatch01ContourInputR00.row31.drop 80).take 16) ((RHBatch01ContourInputI00.row31.drop 80).take 16)=true ∧
 ((RHBatch01ContourInputR00.row31.drop 80).take 16).length=16 := by decide +kernel
theorem checked31_06 : check v 15968
 ((RHBatch01ContourInputR00.row31.drop 96).take 16) ((RHBatch01ContourInputI00.row31.drop 96).take 16)=true ∧
 ((RHBatch01ContourInputR00.row31.drop 96).take 16).length=16 := by decide +kernel
theorem checked31_07 : check v 15984
 ((RHBatch01ContourInputR00.row31.drop 112).take 16) ((RHBatch01ContourInputI00.row31.drop 112).take 16)=true ∧
 ((RHBatch01ContourInputR00.row31.drop 112).take 16).length=16 := by decide +kernel
theorem checked31_08 : check v 16000
 ((RHBatch01ContourInputR00.row31.drop 128).take 16) ((RHBatch01ContourInputI00.row31.drop 128).take 16)=true ∧
 ((RHBatch01ContourInputR00.row31.drop 128).take 16).length=16 := by decide +kernel
theorem checked31_09 : check v 16016
 ((RHBatch01ContourInputR00.row31.drop 144).take 16) ((RHBatch01ContourInputI00.row31.drop 144).take 16)=true ∧
 ((RHBatch01ContourInputR00.row31.drop 144).take 16).length=16 := by decide +kernel
theorem checked31_10 : check v 16032
 ((RHBatch01ContourInputR00.row31.drop 160).take 16) ((RHBatch01ContourInputI00.row31.drop 160).take 16)=true ∧
 ((RHBatch01ContourInputR00.row31.drop 160).take 16).length=16 := by decide +kernel
theorem checked31_11 : check v 16048
 ((RHBatch01ContourInputR00.row31.drop 176).take 16) ((RHBatch01ContourInputI00.row31.drop 176).take 16)=true ∧
 ((RHBatch01ContourInputR00.row31.drop 176).take 16).length=16 := by decide +kernel
theorem checked31_12 : check v 16064
 ((RHBatch01ContourInputR00.row31.drop 192).take 16) ((RHBatch01ContourInputI00.row31.drop 192).take 16)=true ∧
 ((RHBatch01ContourInputR00.row31.drop 192).take 16).length=16 := by decide +kernel
theorem checked31_13 : check v 16080
 ((RHBatch01ContourInputR00.row31.drop 208).take 16) ((RHBatch01ContourInputI00.row31.drop 208).take 16)=true ∧
 ((RHBatch01ContourInputR00.row31.drop 208).take 16).length=16 := by decide +kernel
theorem checked31_14 : check v 16096
 ((RHBatch01ContourInputR00.row31.drop 224).take 16) ((RHBatch01ContourInputI00.row31.drop 224).take 16)=true ∧
 ((RHBatch01ContourInputR00.row31.drop 224).take 16).length=16 := by decide +kernel
theorem checked31_15 : check v 16112
 ((RHBatch01ContourInputR00.row31.drop 240).take 16) ((RHBatch01ContourInputI00.row31.drop 240).take 16)=true ∧
 ((RHBatch01ContourInputR00.row31.drop 240).take 16).length=16 := by decide +kernel
theorem checked31_16 : check v 16128
 ((RHBatch01ContourInputR00.row31.drop 256).take 16) ((RHBatch01ContourInputI00.row31.drop 256).take 16)=true ∧
 ((RHBatch01ContourInputR00.row31.drop 256).take 16).length=16 := by decide +kernel
theorem checked31_17 : check v 16144
 ((RHBatch01ContourInputR00.row31.drop 272).take 16) ((RHBatch01ContourInputI00.row31.drop 272).take 16)=true ∧
 ((RHBatch01ContourInputR00.row31.drop 272).take 16).length=16 := by decide +kernel
theorem checked31_18 : check v 16160
 ((RHBatch01ContourInputR00.row31.drop 288).take 16) ((RHBatch01ContourInputI00.row31.drop 288).take 16)=true ∧
 ((RHBatch01ContourInputR00.row31.drop 288).take 16).length=16 := by decide +kernel
theorem checked31_19 : check v 16176
 ((RHBatch01ContourInputR00.row31.drop 304).take 16) ((RHBatch01ContourInputI00.row31.drop 304).take 16)=true ∧
 ((RHBatch01ContourInputR00.row31.drop 304).take 16).length=16 := by decide +kernel
theorem checked31_20 : check v 16192
 ((RHBatch01ContourInputR00.row31.drop 320).take 16) ((RHBatch01ContourInputI00.row31.drop 320).take 16)=true ∧
 ((RHBatch01ContourInputR00.row31.drop 320).take 16).length=16 := by decide +kernel
theorem checked31_21 : check v 16208
 ((RHBatch01ContourInputR00.row31.drop 336).take 16) ((RHBatch01ContourInputI00.row31.drop 336).take 16)=true ∧
 ((RHBatch01ContourInputR00.row31.drop 336).take 16).length=16 := by decide +kernel
theorem checked31_22 : check v 16224
 ((RHBatch01ContourInputR00.row31.drop 352).take 16) ((RHBatch01ContourInputI00.row31.drop 352).take 16)=true ∧
 ((RHBatch01ContourInputR00.row31.drop 352).take 16).length=16 := by decide +kernel
theorem checked31_23 : check v 16240
 ((RHBatch01ContourInputR00.row31.drop 368).take 16) ((RHBatch01ContourInputI00.row31.drop 368).take 16)=true ∧
 ((RHBatch01ContourInputR00.row31.drop 368).take 16).length=16 := by decide +kernel
theorem checked31_24 : check v 16256
 ((RHBatch01ContourInputR00.row31.drop 384).take 16) ((RHBatch01ContourInputI00.row31.drop 384).take 16)=true ∧
 ((RHBatch01ContourInputR00.row31.drop 384).take 16).length=16 := by decide +kernel
theorem checked31_25 : check v 16272
 ((RHBatch01ContourInputR00.row31.drop 400).take 16) ((RHBatch01ContourInputI00.row31.drop 400).take 16)=true ∧
 ((RHBatch01ContourInputR00.row31.drop 400).take 16).length=16 := by decide +kernel
theorem checked31_26 : check v 16288
 ((RHBatch01ContourInputR00.row31.drop 416).take 16) ((RHBatch01ContourInputI00.row31.drop 416).take 16)=true ∧
 ((RHBatch01ContourInputR00.row31.drop 416).take 16).length=16 := by decide +kernel
theorem checked31_27 : check v 16304
 ((RHBatch01ContourInputR00.row31.drop 432).take 16) ((RHBatch01ContourInputI00.row31.drop 432).take 16)=true ∧
 ((RHBatch01ContourInputR00.row31.drop 432).take 16).length=16 := by decide +kernel
theorem checked31_28 : check v 16320
 ((RHBatch01ContourInputR00.row31.drop 448).take 16) ((RHBatch01ContourInputI00.row31.drop 448).take 16)=true ∧
 ((RHBatch01ContourInputR00.row31.drop 448).take 16).length=16 := by decide +kernel
theorem checked31_29 : check v 16336
 ((RHBatch01ContourInputR00.row31.drop 464).take 16) ((RHBatch01ContourInputI00.row31.drop 464).take 16)=true ∧
 ((RHBatch01ContourInputR00.row31.drop 464).take 16).length=16 := by decide +kernel
theorem checked31_30 : check v 16352
 ((RHBatch01ContourInputR00.row31.drop 480).take 16) ((RHBatch01ContourInputI00.row31.drop 480).take 16)=true ∧
 ((RHBatch01ContourInputR00.row31.drop 480).take 16).length=16 := by decide +kernel
theorem checked31_31 : check v 16368
 ((RHBatch01ContourInputR00.row31.drop 496).take 16) ((RHBatch01ContourInputI00.row31.drop 496).take 16)=true ∧
 ((RHBatch01ContourInputR00.row31.drop 496).take 16).length=16 := by decide +kernel
lemma all_checked (b c : Nat) (hb:b<32) (hc:c<32) :
 check v (512*b+16*c) (realRow b c) (imagRow b c)=true ∧ (realRow b c).length=16 := by
 interval_cases b <;> interval_cases c
 · exact checked00_00
 · exact checked00_01
 · exact checked00_02
 · exact checked00_03
 · exact checked00_04
 · exact checked00_05
 · exact checked00_06
 · exact checked00_07
 · exact checked00_08
 · exact checked00_09
 · exact checked00_10
 · exact checked00_11
 · exact checked00_12
 · exact checked00_13
 · exact checked00_14
 · exact checked00_15
 · exact checked00_16
 · exact checked00_17
 · exact checked00_18
 · exact checked00_19
 · exact checked00_20
 · exact checked00_21
 · exact checked00_22
 · exact checked00_23
 · exact checked00_24
 · exact checked00_25
 · exact checked00_26
 · exact checked00_27
 · exact checked00_28
 · exact checked00_29
 · exact checked00_30
 · exact checked00_31
 · exact checked01_00
 · exact checked01_01
 · exact checked01_02
 · exact checked01_03
 · exact checked01_04
 · exact checked01_05
 · exact checked01_06
 · exact checked01_07
 · exact checked01_08
 · exact checked01_09
 · exact checked01_10
 · exact checked01_11
 · exact checked01_12
 · exact checked01_13
 · exact checked01_14
 · exact checked01_15
 · exact checked01_16
 · exact checked01_17
 · exact checked01_18
 · exact checked01_19
 · exact checked01_20
 · exact checked01_21
 · exact checked01_22
 · exact checked01_23
 · exact checked01_24
 · exact checked01_25
 · exact checked01_26
 · exact checked01_27
 · exact checked01_28
 · exact checked01_29
 · exact checked01_30
 · exact checked01_31
 · exact checked02_00
 · exact checked02_01
 · exact checked02_02
 · exact checked02_03
 · exact checked02_04
 · exact checked02_05
 · exact checked02_06
 · exact checked02_07
 · exact checked02_08
 · exact checked02_09
 · exact checked02_10
 · exact checked02_11
 · exact checked02_12
 · exact checked02_13
 · exact checked02_14
 · exact checked02_15
 · exact checked02_16
 · exact checked02_17
 · exact checked02_18
 · exact checked02_19
 · exact checked02_20
 · exact checked02_21
 · exact checked02_22
 · exact checked02_23
 · exact checked02_24
 · exact checked02_25
 · exact checked02_26
 · exact checked02_27
 · exact checked02_28
 · exact checked02_29
 · exact checked02_30
 · exact checked02_31
 · exact checked03_00
 · exact checked03_01
 · exact checked03_02
 · exact checked03_03
 · exact checked03_04
 · exact checked03_05
 · exact checked03_06
 · exact checked03_07
 · exact checked03_08
 · exact checked03_09
 · exact checked03_10
 · exact checked03_11
 · exact checked03_12
 · exact checked03_13
 · exact checked03_14
 · exact checked03_15
 · exact checked03_16
 · exact checked03_17
 · exact checked03_18
 · exact checked03_19
 · exact checked03_20
 · exact checked03_21
 · exact checked03_22
 · exact checked03_23
 · exact checked03_24
 · exact checked03_25
 · exact checked03_26
 · exact checked03_27
 · exact checked03_28
 · exact checked03_29
 · exact checked03_30
 · exact checked03_31
 · exact checked04_00
 · exact checked04_01
 · exact checked04_02
 · exact checked04_03
 · exact checked04_04
 · exact checked04_05
 · exact checked04_06
 · exact checked04_07
 · exact checked04_08
 · exact checked04_09
 · exact checked04_10
 · exact checked04_11
 · exact checked04_12
 · exact checked04_13
 · exact checked04_14
 · exact checked04_15
 · exact checked04_16
 · exact checked04_17
 · exact checked04_18
 · exact checked04_19
 · exact checked04_20
 · exact checked04_21
 · exact checked04_22
 · exact checked04_23
 · exact checked04_24
 · exact checked04_25
 · exact checked04_26
 · exact checked04_27
 · exact checked04_28
 · exact checked04_29
 · exact checked04_30
 · exact checked04_31
 · exact checked05_00
 · exact checked05_01
 · exact checked05_02
 · exact checked05_03
 · exact checked05_04
 · exact checked05_05
 · exact checked05_06
 · exact checked05_07
 · exact checked05_08
 · exact checked05_09
 · exact checked05_10
 · exact checked05_11
 · exact checked05_12
 · exact checked05_13
 · exact checked05_14
 · exact checked05_15
 · exact checked05_16
 · exact checked05_17
 · exact checked05_18
 · exact checked05_19
 · exact checked05_20
 · exact checked05_21
 · exact checked05_22
 · exact checked05_23
 · exact checked05_24
 · exact checked05_25
 · exact checked05_26
 · exact checked05_27
 · exact checked05_28
 · exact checked05_29
 · exact checked05_30
 · exact checked05_31
 · exact checked06_00
 · exact checked06_01
 · exact checked06_02
 · exact checked06_03
 · exact checked06_04
 · exact checked06_05
 · exact checked06_06
 · exact checked06_07
 · exact checked06_08
 · exact checked06_09
 · exact checked06_10
 · exact checked06_11
 · exact checked06_12
 · exact checked06_13
 · exact checked06_14
 · exact checked06_15
 · exact checked06_16
 · exact checked06_17
 · exact checked06_18
 · exact checked06_19
 · exact checked06_20
 · exact checked06_21
 · exact checked06_22
 · exact checked06_23
 · exact checked06_24
 · exact checked06_25
 · exact checked06_26
 · exact checked06_27
 · exact checked06_28
 · exact checked06_29
 · exact checked06_30
 · exact checked06_31
 · exact checked07_00
 · exact checked07_01
 · exact checked07_02
 · exact checked07_03
 · exact checked07_04
 · exact checked07_05
 · exact checked07_06
 · exact checked07_07
 · exact checked07_08
 · exact checked07_09
 · exact checked07_10
 · exact checked07_11
 · exact checked07_12
 · exact checked07_13
 · exact checked07_14
 · exact checked07_15
 · exact checked07_16
 · exact checked07_17
 · exact checked07_18
 · exact checked07_19
 · exact checked07_20
 · exact checked07_21
 · exact checked07_22
 · exact checked07_23
 · exact checked07_24
 · exact checked07_25
 · exact checked07_26
 · exact checked07_27
 · exact checked07_28
 · exact checked07_29
 · exact checked07_30
 · exact checked07_31
 · exact checked08_00
 · exact checked08_01
 · exact checked08_02
 · exact checked08_03
 · exact checked08_04
 · exact checked08_05
 · exact checked08_06
 · exact checked08_07
 · exact checked08_08
 · exact checked08_09
 · exact checked08_10
 · exact checked08_11
 · exact checked08_12
 · exact checked08_13
 · exact checked08_14
 · exact checked08_15
 · exact checked08_16
 · exact checked08_17
 · exact checked08_18
 · exact checked08_19
 · exact checked08_20
 · exact checked08_21
 · exact checked08_22
 · exact checked08_23
 · exact checked08_24
 · exact checked08_25
 · exact checked08_26
 · exact checked08_27
 · exact checked08_28
 · exact checked08_29
 · exact checked08_30
 · exact checked08_31
 · exact checked09_00
 · exact checked09_01
 · exact checked09_02
 · exact checked09_03
 · exact checked09_04
 · exact checked09_05
 · exact checked09_06
 · exact checked09_07
 · exact checked09_08
 · exact checked09_09
 · exact checked09_10
 · exact checked09_11
 · exact checked09_12
 · exact checked09_13
 · exact checked09_14
 · exact checked09_15
 · exact checked09_16
 · exact checked09_17
 · exact checked09_18
 · exact checked09_19
 · exact checked09_20
 · exact checked09_21
 · exact checked09_22
 · exact checked09_23
 · exact checked09_24
 · exact checked09_25
 · exact checked09_26
 · exact checked09_27
 · exact checked09_28
 · exact checked09_29
 · exact checked09_30
 · exact checked09_31
 · exact checked10_00
 · exact checked10_01
 · exact checked10_02
 · exact checked10_03
 · exact checked10_04
 · exact checked10_05
 · exact checked10_06
 · exact checked10_07
 · exact checked10_08
 · exact checked10_09
 · exact checked10_10
 · exact checked10_11
 · exact checked10_12
 · exact checked10_13
 · exact checked10_14
 · exact checked10_15
 · exact checked10_16
 · exact checked10_17
 · exact checked10_18
 · exact checked10_19
 · exact checked10_20
 · exact checked10_21
 · exact checked10_22
 · exact checked10_23
 · exact checked10_24
 · exact checked10_25
 · exact checked10_26
 · exact checked10_27
 · exact checked10_28
 · exact checked10_29
 · exact checked10_30
 · exact checked10_31
 · exact checked11_00
 · exact checked11_01
 · exact checked11_02
 · exact checked11_03
 · exact checked11_04
 · exact checked11_05
 · exact checked11_06
 · exact checked11_07
 · exact checked11_08
 · exact checked11_09
 · exact checked11_10
 · exact checked11_11
 · exact checked11_12
 · exact checked11_13
 · exact checked11_14
 · exact checked11_15
 · exact checked11_16
 · exact checked11_17
 · exact checked11_18
 · exact checked11_19
 · exact checked11_20
 · exact checked11_21
 · exact checked11_22
 · exact checked11_23
 · exact checked11_24
 · exact checked11_25
 · exact checked11_26
 · exact checked11_27
 · exact checked11_28
 · exact checked11_29
 · exact checked11_30
 · exact checked11_31
 · exact checked12_00
 · exact checked12_01
 · exact checked12_02
 · exact checked12_03
 · exact checked12_04
 · exact checked12_05
 · exact checked12_06
 · exact checked12_07
 · exact checked12_08
 · exact checked12_09
 · exact checked12_10
 · exact checked12_11
 · exact checked12_12
 · exact checked12_13
 · exact checked12_14
 · exact checked12_15
 · exact checked12_16
 · exact checked12_17
 · exact checked12_18
 · exact checked12_19
 · exact checked12_20
 · exact checked12_21
 · exact checked12_22
 · exact checked12_23
 · exact checked12_24
 · exact checked12_25
 · exact checked12_26
 · exact checked12_27
 · exact checked12_28
 · exact checked12_29
 · exact checked12_30
 · exact checked12_31
 · exact checked13_00
 · exact checked13_01
 · exact checked13_02
 · exact checked13_03
 · exact checked13_04
 · exact checked13_05
 · exact checked13_06
 · exact checked13_07
 · exact checked13_08
 · exact checked13_09
 · exact checked13_10
 · exact checked13_11
 · exact checked13_12
 · exact checked13_13
 · exact checked13_14
 · exact checked13_15
 · exact checked13_16
 · exact checked13_17
 · exact checked13_18
 · exact checked13_19
 · exact checked13_20
 · exact checked13_21
 · exact checked13_22
 · exact checked13_23
 · exact checked13_24
 · exact checked13_25
 · exact checked13_26
 · exact checked13_27
 · exact checked13_28
 · exact checked13_29
 · exact checked13_30
 · exact checked13_31
 · exact checked14_00
 · exact checked14_01
 · exact checked14_02
 · exact checked14_03
 · exact checked14_04
 · exact checked14_05
 · exact checked14_06
 · exact checked14_07
 · exact checked14_08
 · exact checked14_09
 · exact checked14_10
 · exact checked14_11
 · exact checked14_12
 · exact checked14_13
 · exact checked14_14
 · exact checked14_15
 · exact checked14_16
 · exact checked14_17
 · exact checked14_18
 · exact checked14_19
 · exact checked14_20
 · exact checked14_21
 · exact checked14_22
 · exact checked14_23
 · exact checked14_24
 · exact checked14_25
 · exact checked14_26
 · exact checked14_27
 · exact checked14_28
 · exact checked14_29
 · exact checked14_30
 · exact checked14_31
 · exact checked15_00
 · exact checked15_01
 · exact checked15_02
 · exact checked15_03
 · exact checked15_04
 · exact checked15_05
 · exact checked15_06
 · exact checked15_07
 · exact checked15_08
 · exact checked15_09
 · exact checked15_10
 · exact checked15_11
 · exact checked15_12
 · exact checked15_13
 · exact checked15_14
 · exact checked15_15
 · exact checked15_16
 · exact checked15_17
 · exact checked15_18
 · exact checked15_19
 · exact checked15_20
 · exact checked15_21
 · exact checked15_22
 · exact checked15_23
 · exact checked15_24
 · exact checked15_25
 · exact checked15_26
 · exact checked15_27
 · exact checked15_28
 · exact checked15_29
 · exact checked15_30
 · exact checked15_31
 · exact checked16_00
 · exact checked16_01
 · exact checked16_02
 · exact checked16_03
 · exact checked16_04
 · exact checked16_05
 · exact checked16_06
 · exact checked16_07
 · exact checked16_08
 · exact checked16_09
 · exact checked16_10
 · exact checked16_11
 · exact checked16_12
 · exact checked16_13
 · exact checked16_14
 · exact checked16_15
 · exact checked16_16
 · exact checked16_17
 · exact checked16_18
 · exact checked16_19
 · exact checked16_20
 · exact checked16_21
 · exact checked16_22
 · exact checked16_23
 · exact checked16_24
 · exact checked16_25
 · exact checked16_26
 · exact checked16_27
 · exact checked16_28
 · exact checked16_29
 · exact checked16_30
 · exact checked16_31
 · exact checked17_00
 · exact checked17_01
 · exact checked17_02
 · exact checked17_03
 · exact checked17_04
 · exact checked17_05
 · exact checked17_06
 · exact checked17_07
 · exact checked17_08
 · exact checked17_09
 · exact checked17_10
 · exact checked17_11
 · exact checked17_12
 · exact checked17_13
 · exact checked17_14
 · exact checked17_15
 · exact checked17_16
 · exact checked17_17
 · exact checked17_18
 · exact checked17_19
 · exact checked17_20
 · exact checked17_21
 · exact checked17_22
 · exact checked17_23
 · exact checked17_24
 · exact checked17_25
 · exact checked17_26
 · exact checked17_27
 · exact checked17_28
 · exact checked17_29
 · exact checked17_30
 · exact checked17_31
 · exact checked18_00
 · exact checked18_01
 · exact checked18_02
 · exact checked18_03
 · exact checked18_04
 · exact checked18_05
 · exact checked18_06
 · exact checked18_07
 · exact checked18_08
 · exact checked18_09
 · exact checked18_10
 · exact checked18_11
 · exact checked18_12
 · exact checked18_13
 · exact checked18_14
 · exact checked18_15
 · exact checked18_16
 · exact checked18_17
 · exact checked18_18
 · exact checked18_19
 · exact checked18_20
 · exact checked18_21
 · exact checked18_22
 · exact checked18_23
 · exact checked18_24
 · exact checked18_25
 · exact checked18_26
 · exact checked18_27
 · exact checked18_28
 · exact checked18_29
 · exact checked18_30
 · exact checked18_31
 · exact checked19_00
 · exact checked19_01
 · exact checked19_02
 · exact checked19_03
 · exact checked19_04
 · exact checked19_05
 · exact checked19_06
 · exact checked19_07
 · exact checked19_08
 · exact checked19_09
 · exact checked19_10
 · exact checked19_11
 · exact checked19_12
 · exact checked19_13
 · exact checked19_14
 · exact checked19_15
 · exact checked19_16
 · exact checked19_17
 · exact checked19_18
 · exact checked19_19
 · exact checked19_20
 · exact checked19_21
 · exact checked19_22
 · exact checked19_23
 · exact checked19_24
 · exact checked19_25
 · exact checked19_26
 · exact checked19_27
 · exact checked19_28
 · exact checked19_29
 · exact checked19_30
 · exact checked19_31
 · exact checked20_00
 · exact checked20_01
 · exact checked20_02
 · exact checked20_03
 · exact checked20_04
 · exact checked20_05
 · exact checked20_06
 · exact checked20_07
 · exact checked20_08
 · exact checked20_09
 · exact checked20_10
 · exact checked20_11
 · exact checked20_12
 · exact checked20_13
 · exact checked20_14
 · exact checked20_15
 · exact checked20_16
 · exact checked20_17
 · exact checked20_18
 · exact checked20_19
 · exact checked20_20
 · exact checked20_21
 · exact checked20_22
 · exact checked20_23
 · exact checked20_24
 · exact checked20_25
 · exact checked20_26
 · exact checked20_27
 · exact checked20_28
 · exact checked20_29
 · exact checked20_30
 · exact checked20_31
 · exact checked21_00
 · exact checked21_01
 · exact checked21_02
 · exact checked21_03
 · exact checked21_04
 · exact checked21_05
 · exact checked21_06
 · exact checked21_07
 · exact checked21_08
 · exact checked21_09
 · exact checked21_10
 · exact checked21_11
 · exact checked21_12
 · exact checked21_13
 · exact checked21_14
 · exact checked21_15
 · exact checked21_16
 · exact checked21_17
 · exact checked21_18
 · exact checked21_19
 · exact checked21_20
 · exact checked21_21
 · exact checked21_22
 · exact checked21_23
 · exact checked21_24
 · exact checked21_25
 · exact checked21_26
 · exact checked21_27
 · exact checked21_28
 · exact checked21_29
 · exact checked21_30
 · exact checked21_31
 · exact checked22_00
 · exact checked22_01
 · exact checked22_02
 · exact checked22_03
 · exact checked22_04
 · exact checked22_05
 · exact checked22_06
 · exact checked22_07
 · exact checked22_08
 · exact checked22_09
 · exact checked22_10
 · exact checked22_11
 · exact checked22_12
 · exact checked22_13
 · exact checked22_14
 · exact checked22_15
 · exact checked22_16
 · exact checked22_17
 · exact checked22_18
 · exact checked22_19
 · exact checked22_20
 · exact checked22_21
 · exact checked22_22
 · exact checked22_23
 · exact checked22_24
 · exact checked22_25
 · exact checked22_26
 · exact checked22_27
 · exact checked22_28
 · exact checked22_29
 · exact checked22_30
 · exact checked22_31
 · exact checked23_00
 · exact checked23_01
 · exact checked23_02
 · exact checked23_03
 · exact checked23_04
 · exact checked23_05
 · exact checked23_06
 · exact checked23_07
 · exact checked23_08
 · exact checked23_09
 · exact checked23_10
 · exact checked23_11
 · exact checked23_12
 · exact checked23_13
 · exact checked23_14
 · exact checked23_15
 · exact checked23_16
 · exact checked23_17
 · exact checked23_18
 · exact checked23_19
 · exact checked23_20
 · exact checked23_21
 · exact checked23_22
 · exact checked23_23
 · exact checked23_24
 · exact checked23_25
 · exact checked23_26
 · exact checked23_27
 · exact checked23_28
 · exact checked23_29
 · exact checked23_30
 · exact checked23_31
 · exact checked24_00
 · exact checked24_01
 · exact checked24_02
 · exact checked24_03
 · exact checked24_04
 · exact checked24_05
 · exact checked24_06
 · exact checked24_07
 · exact checked24_08
 · exact checked24_09
 · exact checked24_10
 · exact checked24_11
 · exact checked24_12
 · exact checked24_13
 · exact checked24_14
 · exact checked24_15
 · exact checked24_16
 · exact checked24_17
 · exact checked24_18
 · exact checked24_19
 · exact checked24_20
 · exact checked24_21
 · exact checked24_22
 · exact checked24_23
 · exact checked24_24
 · exact checked24_25
 · exact checked24_26
 · exact checked24_27
 · exact checked24_28
 · exact checked24_29
 · exact checked24_30
 · exact checked24_31
 · exact checked25_00
 · exact checked25_01
 · exact checked25_02
 · exact checked25_03
 · exact checked25_04
 · exact checked25_05
 · exact checked25_06
 · exact checked25_07
 · exact checked25_08
 · exact checked25_09
 · exact checked25_10
 · exact checked25_11
 · exact checked25_12
 · exact checked25_13
 · exact checked25_14
 · exact checked25_15
 · exact checked25_16
 · exact checked25_17
 · exact checked25_18
 · exact checked25_19
 · exact checked25_20
 · exact checked25_21
 · exact checked25_22
 · exact checked25_23
 · exact checked25_24
 · exact checked25_25
 · exact checked25_26
 · exact checked25_27
 · exact checked25_28
 · exact checked25_29
 · exact checked25_30
 · exact checked25_31
 · exact checked26_00
 · exact checked26_01
 · exact checked26_02
 · exact checked26_03
 · exact checked26_04
 · exact checked26_05
 · exact checked26_06
 · exact checked26_07
 · exact checked26_08
 · exact checked26_09
 · exact checked26_10
 · exact checked26_11
 · exact checked26_12
 · exact checked26_13
 · exact checked26_14
 · exact checked26_15
 · exact checked26_16
 · exact checked26_17
 · exact checked26_18
 · exact checked26_19
 · exact checked26_20
 · exact checked26_21
 · exact checked26_22
 · exact checked26_23
 · exact checked26_24
 · exact checked26_25
 · exact checked26_26
 · exact checked26_27
 · exact checked26_28
 · exact checked26_29
 · exact checked26_30
 · exact checked26_31
 · exact checked27_00
 · exact checked27_01
 · exact checked27_02
 · exact checked27_03
 · exact checked27_04
 · exact checked27_05
 · exact checked27_06
 · exact checked27_07
 · exact checked27_08
 · exact checked27_09
 · exact checked27_10
 · exact checked27_11
 · exact checked27_12
 · exact checked27_13
 · exact checked27_14
 · exact checked27_15
 · exact checked27_16
 · exact checked27_17
 · exact checked27_18
 · exact checked27_19
 · exact checked27_20
 · exact checked27_21
 · exact checked27_22
 · exact checked27_23
 · exact checked27_24
 · exact checked27_25
 · exact checked27_26
 · exact checked27_27
 · exact checked27_28
 · exact checked27_29
 · exact checked27_30
 · exact checked27_31
 · exact checked28_00
 · exact checked28_01
 · exact checked28_02
 · exact checked28_03
 · exact checked28_04
 · exact checked28_05
 · exact checked28_06
 · exact checked28_07
 · exact checked28_08
 · exact checked28_09
 · exact checked28_10
 · exact checked28_11
 · exact checked28_12
 · exact checked28_13
 · exact checked28_14
 · exact checked28_15
 · exact checked28_16
 · exact checked28_17
 · exact checked28_18
 · exact checked28_19
 · exact checked28_20
 · exact checked28_21
 · exact checked28_22
 · exact checked28_23
 · exact checked28_24
 · exact checked28_25
 · exact checked28_26
 · exact checked28_27
 · exact checked28_28
 · exact checked28_29
 · exact checked28_30
 · exact checked28_31
 · exact checked29_00
 · exact checked29_01
 · exact checked29_02
 · exact checked29_03
 · exact checked29_04
 · exact checked29_05
 · exact checked29_06
 · exact checked29_07
 · exact checked29_08
 · exact checked29_09
 · exact checked29_10
 · exact checked29_11
 · exact checked29_12
 · exact checked29_13
 · exact checked29_14
 · exact checked29_15
 · exact checked29_16
 · exact checked29_17
 · exact checked29_18
 · exact checked29_19
 · exact checked29_20
 · exact checked29_21
 · exact checked29_22
 · exact checked29_23
 · exact checked29_24
 · exact checked29_25
 · exact checked29_26
 · exact checked29_27
 · exact checked29_28
 · exact checked29_29
 · exact checked29_30
 · exact checked29_31
 · exact checked30_00
 · exact checked30_01
 · exact checked30_02
 · exact checked30_03
 · exact checked30_04
 · exact checked30_05
 · exact checked30_06
 · exact checked30_07
 · exact checked30_08
 · exact checked30_09
 · exact checked30_10
 · exact checked30_11
 · exact checked30_12
 · exact checked30_13
 · exact checked30_14
 · exact checked30_15
 · exact checked30_16
 · exact checked30_17
 · exact checked30_18
 · exact checked30_19
 · exact checked30_20
 · exact checked30_21
 · exact checked30_22
 · exact checked30_23
 · exact checked30_24
 · exact checked30_25
 · exact checked30_26
 · exact checked30_27
 · exact checked30_28
 · exact checked30_29
 · exact checked30_30
 · exact checked30_31
 · exact checked31_00
 · exact checked31_01
 · exact checked31_02
 · exact checked31_03
 · exact checked31_04
 · exact checked31_05
 · exact checked31_06
 · exact checked31_07
 · exact checked31_08
 · exact checked31_09
 · exact checked31_10
 · exact checked31_11
 · exact checked31_12
 · exact checked31_13
 · exact checked31_14
 · exact checked31_15
 · exact checked31_16
 · exact checked31_17
 · exact checked31_18
 · exact checked31_19
 · exact checked31_20
 · exact checked31_21
 · exact checked31_22
 · exact checked31_23
 · exact checked31_24
 · exact checked31_25
 · exact checked31_26
 · exact checked31_27
 · exact checked31_28
 · exact checked31_29
 · exact checked31_30
 · exact checked31_31
lemma all_raw (b c j : Nat) (hb:b<32) (hc:c<32) (hj:j<16) :
 RHHighContourVector.raw v RHHighFFTArithmeticBase.chirp (512*b+16*c+j)=
  (((((RHBatch01ContourInputR00.rows[b]?).getD [])[16*c+j]?).getD 0:Int)-2^166,
   ((((RHBatch01ContourInputI00.rows[b]?).getD [])[16*c+j]?).getD 0:Int)-2^166) ∧
  ((((RHBatch01ContourInputR00.rows[b]?).getD [])[16*c+j]?).getD 0)≤2^167 ∧
  ((((RHBatch01ContourInputI00.rows[b]?).getD [])[16*c+j]?).getD 0)≤2^167 := by
 have h:=all_checked b c hb hc
 have hh:=sound v (realRow b c) (imagRow b c) (512*b+16*c) j (by rw [h.2];exact hj) h.1
 simpa only [realRow,imagRow,List.getElem?_take,List.getElem?_drop,hj,if_true] using hh
end RHBatch01ActualContourInputUpperNeg64K00
theorem solution :
 ∀ i : Nat,i<16384 →
 RHHighContourVector.raw RHBatch01ContourSpectrumUpperNeg64K00.rows.flatten RHHighFFTArithmeticBase.chirp i=
  (((((RHBatch01ContourInputR00.rows[i/512]?).getD [])[i%512]?).getD 0:Int)-2^166,
   ((((RHBatch01ContourInputI00.rows[i/512]?).getD [])[i%512]?).getD 0:Int)-2^166) ∧
  ((((RHBatch01ContourInputR00.rows[i/512]?).getD [])[i%512]?).getD 0)≤2^167 ∧
  ((((RHBatch01ContourInputI00.rows[i/512]?).getD [])[i%512]?).getD 0)≤2^167 := by
 intro i hi
 let b:=i/512
 let c:=(i%512)/16
 let j:=i%16
 have h:=RHBatch01ActualContourInputUpperNeg64K00.all_raw b c j (by dsimp [b];omega) (by dsimp [c];omega) (by dsimp [j];omega)
 have hi':512*b+16*c+j=i:=by dsimp [b,c,j];omega
 have hcj:16*c+j=i%512:=by dsimp [c,j];omega
 rw [hi',hcj] at h
 exact h
#print axioms solution
