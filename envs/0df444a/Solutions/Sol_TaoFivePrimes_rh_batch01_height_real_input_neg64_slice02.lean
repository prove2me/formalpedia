-- Prove2me | solution 1 for TaoFivePrimes.rh_batch01_height_real_input_neg64_slice02
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T17:48:52.383356+00:00
-- url     : https://prove2.me/submissions/b627fa56-3459-4004-b5ea-434fbb2781c2

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighContourVector
import Definitions.Def_TaoFivePrimes_RHHighFFTArithmeticBase
import Definitions.Def_TaoFivePrimes_RHBatch01ContourInputRRealNeg64
import Definitions.Def_TaoFivePrimes_RHBatch01ContourInputIRealNeg64
import Definitions.Def_TaoFivePrimes_RHBatch01RealSpectrumNeg64
namespace RHBatch01RealInputNeg64Slice02
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
noncomputable def v : List Nat := RHBatch01RealSpectrumNeg64.rows.flatten
noncomputable def rr (c : Nat) : List Nat := (((RHBatch01ContourInputRRealNeg64.rows[2]?).getD []).drop (16*c)).take 1
noncomputable def ii (c : Nat) : List Nat := (((RHBatch01ContourInputIRealNeg64.rows[2]?).getD []).drop (16*c)).take 1
theorem checked00 : check v 1024
 ((RHBatch01ContourInputRRealNeg64.row02.drop 0).take 1) ((RHBatch01ContourInputIRealNeg64.row02.drop 0).take 1)=true ∧
 ((RHBatch01ContourInputRRealNeg64.row02.drop 0).take 1).length=1 := by decide +kernel
lemma all_checked (c : Nat) (hc:c<1) :
 check v (1024+16*c) (rr c) (ii c)=true ∧ (rr c).length=1 := by
 interval_cases c
 · exact checked00
end RHBatch01RealInputNeg64Slice02
theorem solution :
 ∀i:Nat,i<1 →
 RHHighContourVector.raw RHBatch01RealSpectrumNeg64.rows.flatten RHHighFFTArithmeticBase.chirp (1024+i)=
  ((((((RHBatch01ContourInputRRealNeg64.rows[2]?).getD [])[i]?).getD 0:Nat):Int)-2^166,
   (((((RHBatch01ContourInputIRealNeg64.rows[2]?).getD [])[i]?).getD 0:Nat):Int)-2^166) ∧
  ((((RHBatch01ContourInputRRealNeg64.rows[2]?).getD [])[i]?).getD 0)≤2^167 ∧
  ((((RHBatch01ContourInputIRealNeg64.rows[2]?).getD [])[i]?).getD 0)≤2^167 := by
 intro i hi
 have h:=RHBatch01RealInputNeg64Slice02.all_checked (i/16) (by omega)
 have hh:=RHBatch01RealInputNeg64Slice02.RHBatch01SequentialContourInput.sound RHBatch01RealInputNeg64Slice02.v (RHBatch01RealInputNeg64Slice02.rr (i/16)) (RHBatch01RealInputNeg64Slice02.ii (i/16))
  (1024+16*(i/16)) (i%16) (by rw[h.2];omega) h.1
 have he:16*(i/16)+i%16=i:=by omega
 simpa only[RHBatch01RealInputNeg64Slice02.v,RHBatch01RealInputNeg64Slice02.rr,RHBatch01RealInputNeg64Slice02.ii,List.getElem?_take,List.getElem?_drop,
  show i%16<1 by omega,if_true,show 1024+16*(i/16)+i%16=1024+i by omega,he] using hh
#print axioms solution
