-- Prove2me | solution 1 for TaoFivePrimes.rh_batch01_height_contour_actual_input_upper_neg64_k03_slice30
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T15:53:13.489372+00:00
-- url     : https://prove2.me/submissions/7e3c0b16-782c-4be1-b736-a21411039881

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighContourVector
import Definitions.Def_TaoFivePrimes_RHHighFFTArithmeticBase
import Definitions.Def_TaoFivePrimes_RHBatch01ContourInputRUpperNeg64K03
import Definitions.Def_TaoFivePrimes_RHBatch01ContourInputIUpperNeg64K03
import Definitions.Def_TaoFivePrimes_RHBatch01ContourSpectrumUpperNeg64K03
namespace RHBatch01SparseSliceRHBatch01ContourActualInputUpperNeg64K03B30
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
noncomputable def v : List Nat := RHBatch01ContourSpectrumUpperNeg64K03.rows.flatten
noncomputable def rr (c : Nat) : List Nat := (((RHBatch01ContourInputRUpperNeg64K03.rows[30]?).getD []).drop (16*c)).take 16
noncomputable def ii (c : Nat) : List Nat := (((RHBatch01ContourInputIUpperNeg64K03.rows[30]?).getD []).drop (16*c)).take 16
theorem checked00 : check v 15360
 ((RHBatch01ContourInputRUpperNeg64K03.row30.drop 0).take 16) ((RHBatch01ContourInputIUpperNeg64K03.row30.drop 0).take 16)=true ∧
 ((RHBatch01ContourInputRUpperNeg64K03.row30.drop 0).take 16).length=16 := by decide +kernel
theorem checked01 : check v 15376
 ((RHBatch01ContourInputRUpperNeg64K03.row30.drop 16).take 16) ((RHBatch01ContourInputIUpperNeg64K03.row30.drop 16).take 16)=true ∧
 ((RHBatch01ContourInputRUpperNeg64K03.row30.drop 16).take 16).length=16 := by decide +kernel
theorem checked02 : check v 15392
 ((RHBatch01ContourInputRUpperNeg64K03.row30.drop 32).take 16) ((RHBatch01ContourInputIUpperNeg64K03.row30.drop 32).take 16)=true ∧
 ((RHBatch01ContourInputRUpperNeg64K03.row30.drop 32).take 16).length=16 := by decide +kernel
theorem checked03 : check v 15408
 ((RHBatch01ContourInputRUpperNeg64K03.row30.drop 48).take 16) ((RHBatch01ContourInputIUpperNeg64K03.row30.drop 48).take 16)=true ∧
 ((RHBatch01ContourInputRUpperNeg64K03.row30.drop 48).take 16).length=16 := by decide +kernel
theorem checked04 : check v 15424
 ((RHBatch01ContourInputRUpperNeg64K03.row30.drop 64).take 16) ((RHBatch01ContourInputIUpperNeg64K03.row30.drop 64).take 16)=true ∧
 ((RHBatch01ContourInputRUpperNeg64K03.row30.drop 64).take 16).length=16 := by decide +kernel
theorem checked05 : check v 15440
 ((RHBatch01ContourInputRUpperNeg64K03.row30.drop 80).take 16) ((RHBatch01ContourInputIUpperNeg64K03.row30.drop 80).take 16)=true ∧
 ((RHBatch01ContourInputRUpperNeg64K03.row30.drop 80).take 16).length=16 := by decide +kernel
theorem checked06 : check v 15456
 ((RHBatch01ContourInputRUpperNeg64K03.row30.drop 96).take 16) ((RHBatch01ContourInputIUpperNeg64K03.row30.drop 96).take 16)=true ∧
 ((RHBatch01ContourInputRUpperNeg64K03.row30.drop 96).take 16).length=16 := by decide +kernel
theorem checked07 : check v 15472
 ((RHBatch01ContourInputRUpperNeg64K03.row30.drop 112).take 16) ((RHBatch01ContourInputIUpperNeg64K03.row30.drop 112).take 16)=true ∧
 ((RHBatch01ContourInputRUpperNeg64K03.row30.drop 112).take 16).length=16 := by decide +kernel
theorem checked08 : check v 15488
 ((RHBatch01ContourInputRUpperNeg64K03.row30.drop 128).take 16) ((RHBatch01ContourInputIUpperNeg64K03.row30.drop 128).take 16)=true ∧
 ((RHBatch01ContourInputRUpperNeg64K03.row30.drop 128).take 16).length=16 := by decide +kernel
theorem checked09 : check v 15504
 ((RHBatch01ContourInputRUpperNeg64K03.row30.drop 144).take 16) ((RHBatch01ContourInputIUpperNeg64K03.row30.drop 144).take 16)=true ∧
 ((RHBatch01ContourInputRUpperNeg64K03.row30.drop 144).take 16).length=16 := by decide +kernel
theorem checked10 : check v 15520
 ((RHBatch01ContourInputRUpperNeg64K03.row30.drop 160).take 16) ((RHBatch01ContourInputIUpperNeg64K03.row30.drop 160).take 16)=true ∧
 ((RHBatch01ContourInputRUpperNeg64K03.row30.drop 160).take 16).length=16 := by decide +kernel
theorem checked11 : check v 15536
 ((RHBatch01ContourInputRUpperNeg64K03.row30.drop 176).take 16) ((RHBatch01ContourInputIUpperNeg64K03.row30.drop 176).take 16)=true ∧
 ((RHBatch01ContourInputRUpperNeg64K03.row30.drop 176).take 16).length=16 := by decide +kernel
theorem checked12 : check v 15552
 ((RHBatch01ContourInputRUpperNeg64K03.row30.drop 192).take 16) ((RHBatch01ContourInputIUpperNeg64K03.row30.drop 192).take 16)=true ∧
 ((RHBatch01ContourInputRUpperNeg64K03.row30.drop 192).take 16).length=16 := by decide +kernel
theorem checked13 : check v 15568
 ((RHBatch01ContourInputRUpperNeg64K03.row30.drop 208).take 16) ((RHBatch01ContourInputIUpperNeg64K03.row30.drop 208).take 16)=true ∧
 ((RHBatch01ContourInputRUpperNeg64K03.row30.drop 208).take 16).length=16 := by decide +kernel
theorem checked14 : check v 15584
 ((RHBatch01ContourInputRUpperNeg64K03.row30.drop 224).take 16) ((RHBatch01ContourInputIUpperNeg64K03.row30.drop 224).take 16)=true ∧
 ((RHBatch01ContourInputRUpperNeg64K03.row30.drop 224).take 16).length=16 := by decide +kernel
theorem checked15 : check v 15600
 ((RHBatch01ContourInputRUpperNeg64K03.row30.drop 240).take 16) ((RHBatch01ContourInputIUpperNeg64K03.row30.drop 240).take 16)=true ∧
 ((RHBatch01ContourInputRUpperNeg64K03.row30.drop 240).take 16).length=16 := by decide +kernel
theorem checked16 : check v 15616
 ((RHBatch01ContourInputRUpperNeg64K03.row30.drop 256).take 16) ((RHBatch01ContourInputIUpperNeg64K03.row30.drop 256).take 16)=true ∧
 ((RHBatch01ContourInputRUpperNeg64K03.row30.drop 256).take 16).length=16 := by decide +kernel
theorem checked17 : check v 15632
 ((RHBatch01ContourInputRUpperNeg64K03.row30.drop 272).take 16) ((RHBatch01ContourInputIUpperNeg64K03.row30.drop 272).take 16)=true ∧
 ((RHBatch01ContourInputRUpperNeg64K03.row30.drop 272).take 16).length=16 := by decide +kernel
theorem checked18 : check v 15648
 ((RHBatch01ContourInputRUpperNeg64K03.row30.drop 288).take 16) ((RHBatch01ContourInputIUpperNeg64K03.row30.drop 288).take 16)=true ∧
 ((RHBatch01ContourInputRUpperNeg64K03.row30.drop 288).take 16).length=16 := by decide +kernel
theorem checked19 : check v 15664
 ((RHBatch01ContourInputRUpperNeg64K03.row30.drop 304).take 16) ((RHBatch01ContourInputIUpperNeg64K03.row30.drop 304).take 16)=true ∧
 ((RHBatch01ContourInputRUpperNeg64K03.row30.drop 304).take 16).length=16 := by decide +kernel
theorem checked20 : check v 15680
 ((RHBatch01ContourInputRUpperNeg64K03.row30.drop 320).take 16) ((RHBatch01ContourInputIUpperNeg64K03.row30.drop 320).take 16)=true ∧
 ((RHBatch01ContourInputRUpperNeg64K03.row30.drop 320).take 16).length=16 := by decide +kernel
theorem checked21 : check v 15696
 ((RHBatch01ContourInputRUpperNeg64K03.row30.drop 336).take 16) ((RHBatch01ContourInputIUpperNeg64K03.row30.drop 336).take 16)=true ∧
 ((RHBatch01ContourInputRUpperNeg64K03.row30.drop 336).take 16).length=16 := by decide +kernel
theorem checked22 : check v 15712
 ((RHBatch01ContourInputRUpperNeg64K03.row30.drop 352).take 16) ((RHBatch01ContourInputIUpperNeg64K03.row30.drop 352).take 16)=true ∧
 ((RHBatch01ContourInputRUpperNeg64K03.row30.drop 352).take 16).length=16 := by decide +kernel
theorem checked23 : check v 15728
 ((RHBatch01ContourInputRUpperNeg64K03.row30.drop 368).take 16) ((RHBatch01ContourInputIUpperNeg64K03.row30.drop 368).take 16)=true ∧
 ((RHBatch01ContourInputRUpperNeg64K03.row30.drop 368).take 16).length=16 := by decide +kernel
theorem checked24 : check v 15744
 ((RHBatch01ContourInputRUpperNeg64K03.row30.drop 384).take 16) ((RHBatch01ContourInputIUpperNeg64K03.row30.drop 384).take 16)=true ∧
 ((RHBatch01ContourInputRUpperNeg64K03.row30.drop 384).take 16).length=16 := by decide +kernel
theorem checked25 : check v 15760
 ((RHBatch01ContourInputRUpperNeg64K03.row30.drop 400).take 16) ((RHBatch01ContourInputIUpperNeg64K03.row30.drop 400).take 16)=true ∧
 ((RHBatch01ContourInputRUpperNeg64K03.row30.drop 400).take 16).length=16 := by decide +kernel
theorem checked26 : check v 15776
 ((RHBatch01ContourInputRUpperNeg64K03.row30.drop 416).take 16) ((RHBatch01ContourInputIUpperNeg64K03.row30.drop 416).take 16)=true ∧
 ((RHBatch01ContourInputRUpperNeg64K03.row30.drop 416).take 16).length=16 := by decide +kernel
theorem checked27 : check v 15792
 ((RHBatch01ContourInputRUpperNeg64K03.row30.drop 432).take 16) ((RHBatch01ContourInputIUpperNeg64K03.row30.drop 432).take 16)=true ∧
 ((RHBatch01ContourInputRUpperNeg64K03.row30.drop 432).take 16).length=16 := by decide +kernel
theorem checked28 : check v 15808
 ((RHBatch01ContourInputRUpperNeg64K03.row30.drop 448).take 16) ((RHBatch01ContourInputIUpperNeg64K03.row30.drop 448).take 16)=true ∧
 ((RHBatch01ContourInputRUpperNeg64K03.row30.drop 448).take 16).length=16 := by decide +kernel
theorem checked29 : check v 15824
 ((RHBatch01ContourInputRUpperNeg64K03.row30.drop 464).take 16) ((RHBatch01ContourInputIUpperNeg64K03.row30.drop 464).take 16)=true ∧
 ((RHBatch01ContourInputRUpperNeg64K03.row30.drop 464).take 16).length=16 := by decide +kernel
theorem checked30 : check v 15840
 ((RHBatch01ContourInputRUpperNeg64K03.row30.drop 480).take 16) ((RHBatch01ContourInputIUpperNeg64K03.row30.drop 480).take 16)=true ∧
 ((RHBatch01ContourInputRUpperNeg64K03.row30.drop 480).take 16).length=16 := by decide +kernel
theorem checked31 : check v 15856
 ((RHBatch01ContourInputRUpperNeg64K03.row30.drop 496).take 16) ((RHBatch01ContourInputIUpperNeg64K03.row30.drop 496).take 16)=true ∧
 ((RHBatch01ContourInputRUpperNeg64K03.row30.drop 496).take 16).length=16 := by decide +kernel
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
end RHBatch01SparseSliceRHBatch01ContourActualInputUpperNeg64K03B30
theorem solution :
 ∀i:Nat,i<512 →
 RHHighContourVector.raw RHBatch01ContourSpectrumUpperNeg64K03.rows.flatten RHHighFFTArithmeticBase.chirp (15360+i)=
  ((((((RHBatch01ContourInputRUpperNeg64K03.rows[30]?).getD [])[i]?).getD 0:Nat):Int)-2^166,
   (((((RHBatch01ContourInputIUpperNeg64K03.rows[30]?).getD [])[i]?).getD 0:Nat):Int)-2^166) ∧
  ((((RHBatch01ContourInputRUpperNeg64K03.rows[30]?).getD [])[i]?).getD 0)≤2^167 ∧
  ((((RHBatch01ContourInputIUpperNeg64K03.rows[30]?).getD [])[i]?).getD 0)≤2^167 := by
 intro i hi
 have h:=RHBatch01SparseSliceRHBatch01ContourActualInputUpperNeg64K03B30.all_checked (i/16) (by omega)
 have hh:=RHBatch01SparseSliceRHBatch01ContourActualInputUpperNeg64K03B30.RHBatch01SequentialContourInput.sound RHBatch01SparseSliceRHBatch01ContourActualInputUpperNeg64K03B30.v (RHBatch01SparseSliceRHBatch01ContourActualInputUpperNeg64K03B30.rr (i/16)) (RHBatch01SparseSliceRHBatch01ContourActualInputUpperNeg64K03B30.ii (i/16))
  (15360+16*(i/16)) (i%16) (by rw[h.2];omega) h.1
 have he:16*(i/16)+i%16=i:=by omega
 simpa only[RHBatch01SparseSliceRHBatch01ContourActualInputUpperNeg64K03B30.v,RHBatch01SparseSliceRHBatch01ContourActualInputUpperNeg64K03B30.rr,RHBatch01SparseSliceRHBatch01ContourActualInputUpperNeg64K03B30.ii,List.getElem?_take,List.getElem?_drop,
  show i%16<16 by omega,if_true,show 15360+16*(i/16)+i%16=15360+i by omega,he] using hh
#print axioms solution
