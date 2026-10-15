-- Prove2me | solution 1 for TaoFivePrimes.rh_high_height_real_input_neg64_slice02
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T08:43:15.496188+00:00
-- url     : https://prove2.me/submissions/ff0b5717-487d-4d5e-9b65-8b1e0e8a1acb

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighContourVector
import Definitions.Def_TaoFivePrimes_RHHighFFTArithmeticBase
import Definitions.Def_TaoFivePrimes_RHHighContourInputRRealNeg64
import Definitions.Def_TaoFivePrimes_RHHighContourInputIRealNeg64
import Definitions.Def_TaoFivePrimes_RHHighRealSpectrumNeg64
namespace RHHighRealInputNeg64Slice02
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
noncomputable def rr (c : Nat) : List Nat := (((RHHighContourInputRRealNeg64.rows[2]?).getD []).drop (16*c)).take 1
noncomputable def ii (c : Nat) : List Nat := (((RHHighContourInputIRealNeg64.rows[2]?).getD []).drop (16*c)).take 1
theorem checked00 : check v 1024
 ((RHHighContourInputRRealNeg64.row02.drop 0).take 1) ((RHHighContourInputIRealNeg64.row02.drop 0).take 1)=true ∧
 ((RHHighContourInputRRealNeg64.row02.drop 0).take 1).length=1 := by decide +kernel
lemma all_checked (c : Nat) (hc:c<1) :
 check v (1024+16*c) (rr c) (ii c)=true ∧ (rr c).length=1 := by
 interval_cases c
 · exact checked00
end RHHighRealInputNeg64Slice02
theorem solution :
 ∀i:Nat,i<1 →
 RHHighContourVector.raw RHHighRealSpectrumNeg64.rows.flatten RHHighFFTArithmeticBase.chirp (1024+i)=
  ((((((RHHighContourInputRRealNeg64.rows[2]?).getD [])[i]?).getD 0:Nat):Int)-2^166,
   (((((RHHighContourInputIRealNeg64.rows[2]?).getD [])[i]?).getD 0:Nat):Int)-2^166) ∧
  ((((RHHighContourInputRRealNeg64.rows[2]?).getD [])[i]?).getD 0)≤2^167 ∧
  ((((RHHighContourInputIRealNeg64.rows[2]?).getD [])[i]?).getD 0)≤2^167 := by
 intro i hi
 have h:=RHHighRealInputNeg64Slice02.all_checked (i/16) (by omega)
 have hh:=RHHighRealInputNeg64Slice02.RHHighSequentialContourInput.sound RHHighRealInputNeg64Slice02.v (RHHighRealInputNeg64Slice02.rr (i/16)) (RHHighRealInputNeg64Slice02.ii (i/16))
  (1024+16*(i/16)) (i%16) (by rw[h.2];omega) h.1
 have he:16*(i/16)+i%16=i:=by omega
 simpa only[RHHighRealInputNeg64Slice02.v,RHHighRealInputNeg64Slice02.rr,RHHighRealInputNeg64Slice02.ii,List.getElem?_take,List.getElem?_drop,
  show i%16<1 by omega,if_true,show 1024+16*(i/16)+i%16=1024+i by omega,he] using hh
