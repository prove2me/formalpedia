-- Prove2me | solution 1 for TaoFivePrimes.rh_high_height_real_input_neg64_slice01
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T08:43:36.978935+00:00
-- url     : https://prove2.me/submissions/587c1c91-e0ba-4a5e-bbdd-92291420f3f5

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighContourVector
import Definitions.Def_TaoFivePrimes_RHHighFFTArithmeticBase
import Definitions.Def_TaoFivePrimes_RHHighContourInputRRealNeg64
import Definitions.Def_TaoFivePrimes_RHHighContourInputIRealNeg64
import Definitions.Def_TaoFivePrimes_RHHighRealSpectrumNeg64
namespace RHHighRealInputNeg64Slice01
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace RHHighSequentialContourInput
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
end RHHighSequentialContourInput
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
open RHHighSequentialContourInput
noncomputable def v : List Nat := RHHighRealSpectrumNeg64.rows.flatten
noncomputable def rr (c : Nat) : List Nat := (((RHHighContourInputRRealNeg64.rows[1]?).getD []).drop (16*c)).take 16
noncomputable def ii (c : Nat) : List Nat := (((RHHighContourInputIRealNeg64.rows[1]?).getD []).drop (16*c)).take 16
theorem checked00 : check v 512
 ((RHHighContourInputRRealNeg64.row01.drop 0).take 16) ((RHHighContourInputIRealNeg64.row01.drop 0).take 16)=true ∧
 ((RHHighContourInputRRealNeg64.row01.drop 0).take 16).length=16 := by decide +kernel
theorem checked01 : check v 528
 ((RHHighContourInputRRealNeg64.row01.drop 16).take 16) ((RHHighContourInputIRealNeg64.row01.drop 16).take 16)=true ∧
 ((RHHighContourInputRRealNeg64.row01.drop 16).take 16).length=16 := by decide +kernel
theorem checked02 : check v 544
 ((RHHighContourInputRRealNeg64.row01.drop 32).take 16) ((RHHighContourInputIRealNeg64.row01.drop 32).take 16)=true ∧
 ((RHHighContourInputRRealNeg64.row01.drop 32).take 16).length=16 := by decide +kernel
theorem checked03 : check v 560
 ((RHHighContourInputRRealNeg64.row01.drop 48).take 16) ((RHHighContourInputIRealNeg64.row01.drop 48).take 16)=true ∧
 ((RHHighContourInputRRealNeg64.row01.drop 48).take 16).length=16 := by decide +kernel
theorem checked04 : check v 576
 ((RHHighContourInputRRealNeg64.row01.drop 64).take 16) ((RHHighContourInputIRealNeg64.row01.drop 64).take 16)=true ∧
 ((RHHighContourInputRRealNeg64.row01.drop 64).take 16).length=16 := by decide +kernel
theorem checked05 : check v 592
 ((RHHighContourInputRRealNeg64.row01.drop 80).take 16) ((RHHighContourInputIRealNeg64.row01.drop 80).take 16)=true ∧
 ((RHHighContourInputRRealNeg64.row01.drop 80).take 16).length=16 := by decide +kernel
theorem checked06 : check v 608
 ((RHHighContourInputRRealNeg64.row01.drop 96).take 16) ((RHHighContourInputIRealNeg64.row01.drop 96).take 16)=true ∧
 ((RHHighContourInputRRealNeg64.row01.drop 96).take 16).length=16 := by decide +kernel
theorem checked07 : check v 624
 ((RHHighContourInputRRealNeg64.row01.drop 112).take 16) ((RHHighContourInputIRealNeg64.row01.drop 112).take 16)=true ∧
 ((RHHighContourInputRRealNeg64.row01.drop 112).take 16).length=16 := by decide +kernel
theorem checked08 : check v 640
 ((RHHighContourInputRRealNeg64.row01.drop 128).take 16) ((RHHighContourInputIRealNeg64.row01.drop 128).take 16)=true ∧
 ((RHHighContourInputRRealNeg64.row01.drop 128).take 16).length=16 := by decide +kernel
theorem checked09 : check v 656
 ((RHHighContourInputRRealNeg64.row01.drop 144).take 16) ((RHHighContourInputIRealNeg64.row01.drop 144).take 16)=true ∧
 ((RHHighContourInputRRealNeg64.row01.drop 144).take 16).length=16 := by decide +kernel
theorem checked10 : check v 672
 ((RHHighContourInputRRealNeg64.row01.drop 160).take 16) ((RHHighContourInputIRealNeg64.row01.drop 160).take 16)=true ∧
 ((RHHighContourInputRRealNeg64.row01.drop 160).take 16).length=16 := by decide +kernel
theorem checked11 : check v 688
 ((RHHighContourInputRRealNeg64.row01.drop 176).take 16) ((RHHighContourInputIRealNeg64.row01.drop 176).take 16)=true ∧
 ((RHHighContourInputRRealNeg64.row01.drop 176).take 16).length=16 := by decide +kernel
theorem checked12 : check v 704
 ((RHHighContourInputRRealNeg64.row01.drop 192).take 16) ((RHHighContourInputIRealNeg64.row01.drop 192).take 16)=true ∧
 ((RHHighContourInputRRealNeg64.row01.drop 192).take 16).length=16 := by decide +kernel
theorem checked13 : check v 720
 ((RHHighContourInputRRealNeg64.row01.drop 208).take 16) ((RHHighContourInputIRealNeg64.row01.drop 208).take 16)=true ∧
 ((RHHighContourInputRRealNeg64.row01.drop 208).take 16).length=16 := by decide +kernel
theorem checked14 : check v 736
 ((RHHighContourInputRRealNeg64.row01.drop 224).take 16) ((RHHighContourInputIRealNeg64.row01.drop 224).take 16)=true ∧
 ((RHHighContourInputRRealNeg64.row01.drop 224).take 16).length=16 := by decide +kernel
theorem checked15 : check v 752
 ((RHHighContourInputRRealNeg64.row01.drop 240).take 16) ((RHHighContourInputIRealNeg64.row01.drop 240).take 16)=true ∧
 ((RHHighContourInputRRealNeg64.row01.drop 240).take 16).length=16 := by decide +kernel
theorem checked16 : check v 768
 ((RHHighContourInputRRealNeg64.row01.drop 256).take 16) ((RHHighContourInputIRealNeg64.row01.drop 256).take 16)=true ∧
 ((RHHighContourInputRRealNeg64.row01.drop 256).take 16).length=16 := by decide +kernel
theorem checked17 : check v 784
 ((RHHighContourInputRRealNeg64.row01.drop 272).take 16) ((RHHighContourInputIRealNeg64.row01.drop 272).take 16)=true ∧
 ((RHHighContourInputRRealNeg64.row01.drop 272).take 16).length=16 := by decide +kernel
theorem checked18 : check v 800
 ((RHHighContourInputRRealNeg64.row01.drop 288).take 16) ((RHHighContourInputIRealNeg64.row01.drop 288).take 16)=true ∧
 ((RHHighContourInputRRealNeg64.row01.drop 288).take 16).length=16 := by decide +kernel
theorem checked19 : check v 816
 ((RHHighContourInputRRealNeg64.row01.drop 304).take 16) ((RHHighContourInputIRealNeg64.row01.drop 304).take 16)=true ∧
 ((RHHighContourInputRRealNeg64.row01.drop 304).take 16).length=16 := by decide +kernel
theorem checked20 : check v 832
 ((RHHighContourInputRRealNeg64.row01.drop 320).take 16) ((RHHighContourInputIRealNeg64.row01.drop 320).take 16)=true ∧
 ((RHHighContourInputRRealNeg64.row01.drop 320).take 16).length=16 := by decide +kernel
theorem checked21 : check v 848
 ((RHHighContourInputRRealNeg64.row01.drop 336).take 16) ((RHHighContourInputIRealNeg64.row01.drop 336).take 16)=true ∧
 ((RHHighContourInputRRealNeg64.row01.drop 336).take 16).length=16 := by decide +kernel
theorem checked22 : check v 864
 ((RHHighContourInputRRealNeg64.row01.drop 352).take 16) ((RHHighContourInputIRealNeg64.row01.drop 352).take 16)=true ∧
 ((RHHighContourInputRRealNeg64.row01.drop 352).take 16).length=16 := by decide +kernel
theorem checked23 : check v 880
 ((RHHighContourInputRRealNeg64.row01.drop 368).take 16) ((RHHighContourInputIRealNeg64.row01.drop 368).take 16)=true ∧
 ((RHHighContourInputRRealNeg64.row01.drop 368).take 16).length=16 := by decide +kernel
theorem checked24 : check v 896
 ((RHHighContourInputRRealNeg64.row01.drop 384).take 16) ((RHHighContourInputIRealNeg64.row01.drop 384).take 16)=true ∧
 ((RHHighContourInputRRealNeg64.row01.drop 384).take 16).length=16 := by decide +kernel
theorem checked25 : check v 912
 ((RHHighContourInputRRealNeg64.row01.drop 400).take 16) ((RHHighContourInputIRealNeg64.row01.drop 400).take 16)=true ∧
 ((RHHighContourInputRRealNeg64.row01.drop 400).take 16).length=16 := by decide +kernel
theorem checked26 : check v 928
 ((RHHighContourInputRRealNeg64.row01.drop 416).take 16) ((RHHighContourInputIRealNeg64.row01.drop 416).take 16)=true ∧
 ((RHHighContourInputRRealNeg64.row01.drop 416).take 16).length=16 := by decide +kernel
theorem checked27 : check v 944
 ((RHHighContourInputRRealNeg64.row01.drop 432).take 16) ((RHHighContourInputIRealNeg64.row01.drop 432).take 16)=true ∧
 ((RHHighContourInputRRealNeg64.row01.drop 432).take 16).length=16 := by decide +kernel
theorem checked28 : check v 960
 ((RHHighContourInputRRealNeg64.row01.drop 448).take 16) ((RHHighContourInputIRealNeg64.row01.drop 448).take 16)=true ∧
 ((RHHighContourInputRRealNeg64.row01.drop 448).take 16).length=16 := by decide +kernel
theorem checked29 : check v 976
 ((RHHighContourInputRRealNeg64.row01.drop 464).take 16) ((RHHighContourInputIRealNeg64.row01.drop 464).take 16)=true ∧
 ((RHHighContourInputRRealNeg64.row01.drop 464).take 16).length=16 := by decide +kernel
theorem checked30 : check v 992
 ((RHHighContourInputRRealNeg64.row01.drop 480).take 16) ((RHHighContourInputIRealNeg64.row01.drop 480).take 16)=true ∧
 ((RHHighContourInputRRealNeg64.row01.drop 480).take 16).length=16 := by decide +kernel
theorem checked31 : check v 1008
 ((RHHighContourInputRRealNeg64.row01.drop 496).take 16) ((RHHighContourInputIRealNeg64.row01.drop 496).take 16)=true ∧
 ((RHHighContourInputRRealNeg64.row01.drop 496).take 16).length=16 := by decide +kernel
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
end RHHighRealInputNeg64Slice01
theorem solution :
 ∀i:Nat,i<512 →
 RHHighContourVector.raw RHHighRealSpectrumNeg64.rows.flatten RHHighFFTArithmeticBase.chirp (512+i)=
  ((((((RHHighContourInputRRealNeg64.rows[1]?).getD [])[i]?).getD 0:Nat):Int)-2^166,
   (((((RHHighContourInputIRealNeg64.rows[1]?).getD [])[i]?).getD 0:Nat):Int)-2^166) ∧
  ((((RHHighContourInputRRealNeg64.rows[1]?).getD [])[i]?).getD 0)≤2^167 ∧
  ((((RHHighContourInputIRealNeg64.rows[1]?).getD [])[i]?).getD 0)≤2^167 := by
 intro i hi
 have h:=RHHighRealInputNeg64Slice01.all_checked (i/16) (by omega)
 have hh:=RHHighRealInputNeg64Slice01.RHHighSequentialContourInput.sound RHHighRealInputNeg64Slice01.v (RHHighRealInputNeg64Slice01.rr (i/16)) (RHHighRealInputNeg64Slice01.ii (i/16))
  (512+16*(i/16)) (i%16) (by rw[h.2];omega) h.1
 have he:16*(i/16)+i%16=i:=by omega
 simpa only[RHHighRealInputNeg64Slice01.v,RHHighRealInputNeg64Slice01.rr,RHHighRealInputNeg64Slice01.ii,List.getElem?_take,List.getElem?_drop,
  show i%16<16 by omega,if_true,show 512+16*(i/16)+i%16=512+i by omega,he] using hh
