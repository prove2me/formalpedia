-- Prove2me | solution 1 for TaoFivePrimes.rh_high_height_fft_actual_input08
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T08:47:19.512569+00:00
-- url     : https://prove2.me/submissions/22004007-30e0-4056-b722-bdf799d4e798

import Theorems.Thm_TaoFivePrimes_rh_high_height_all_moment_word_arithmetic
import Definitions.Def_TaoFivePrimes_RHHighAllMomentWords
import Definitions.Def_TaoFivePrimes_RHHighFFTArithmeticBase
import Definitions.Def_TaoFivePrimes_RHHighFFTInputI08
import Definitions.Def_TaoFivePrimes_RHHighFFTInputR08
import Definitions.Def_TaoFivePrimes_RHHighNormalizedMomentArithmetic
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace RHHighSequentialFFTInputOrder08
noncomputable def check (start k : Nat) : List Nat→List Nat→List Nat→Bool
  | [],[],[] => true
  | p::ps,r::rs,i::is => decide (RHHighFFTArithmeticBase.raw p k start=((r:Int)-2^166,(i:Int)-2^166)) &&
      check (start+1) k ps rs is
  | _,_,_ => false
lemma sound (ps rs is : List Nat) (start k j : Nat) (hj:j<ps.length) (h:check start k ps rs is=true) :
    RHHighFFTArithmeticBase.raw ((ps[j]?).getD 0) k (start+j)=
      ((((rs[j]?).getD 0:Nat):Int)-2^166,(((is[j]?).getD 0:Nat):Int)-2^166) := by
  induction ps generalizing start j rs is with
  | nil => simp at hj
  | cons p ps ih =>
    cases rs with
    | nil => simp [check] at h
    | cons r rs => cases is with
      | nil => simp [check] at h
      | cons i is =>
        simp only [check,Bool.and_eq_true,decide_eq_true_eq] at h
        cases j with
        | zero => simpa only [Nat.add_zero,List.getElem?_cons_zero,Option.getD_some] using h.1
        | succ j =>
          have hh:=ih rs is (start+1) j (by simpa using hj) h.2
          simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,List.getElem?_cons_succ] using hh
end RHHighSequentialFFTInputOrder08

set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace RHHighSequentialFFTAll08
open RHHighSequentialFFTInputOrder08
noncomputable def blocks : List (List (List Nat)) := [RHHighMomentValues00.rows,RHHighMomentValues01.rows,RHHighMomentValues02.rows,RHHighMomentValues03.rows,RHHighMomentValues04.rows,RHHighMomentValues05.rows,RHHighMomentValues06.rows,RHHighMomentValues07.rows,RHHighMomentValues08.rows,RHHighMomentValues09.rows,RHHighMomentValues10.rows,RHHighMomentValues11.rows,RHHighMomentValues12.rows,RHHighMomentValues13.rows,RHHighMomentValues14.rows,RHHighMomentValues15.rows,RHHighMomentValues16.rows,RHHighMomentValues17.rows,RHHighMomentValues18.rows,RHHighMomentValues19.rows,RHHighMomentValues20.rows,RHHighMomentValues21.rows,RHHighMomentValues22.rows,RHHighMomentValues23.rows,RHHighMomentValues24.rows,RHHighMomentValues25.rows,RHHighMomentValues26.rows,RHHighMomentValues27.rows,RHHighMomentValues28.rows,RHHighMomentValues29.rows,RHHighMomentValues30.rows,RHHighMomentValues31.rows]
noncomputable def wordRow (b c : Nat) : List Nat := (((blocks[b]?).getD [])[c]?).getD []
noncomputable def realRow (b c : Nat) : List Nat := (((RHHighFFTInputR08.rows[b]?).getD []).drop (16*c)).take 16
noncomputable def imagRow (b c : Nat) : List Nat := (((RHHighFFTInputI08.rows[b]?).getD []).drop (16*c)).take 16
noncomputable def checkRow (b : Nat) : Bool := (List.range 32).all (fun c=>
 check (512*b+16*c) 8 (wordRow b c) (realRow b c) (imagRow b c) && decide ((wordRow b c).length=16))
theorem row_checked00 : checkRow 0=true := by decide +kernel
theorem row_checked01 : checkRow 1=true := by decide +kernel
theorem row_checked02 : checkRow 2=true := by decide +kernel
theorem row_checked03 : checkRow 3=true := by decide +kernel
theorem row_checked04 : checkRow 4=true := by decide +kernel
theorem row_checked05 : checkRow 5=true := by decide +kernel
theorem row_checked06 : checkRow 6=true := by decide +kernel
theorem row_checked07 : checkRow 7=true := by decide +kernel
theorem row_checked08 : checkRow 8=true := by decide +kernel
theorem row_checked09 : checkRow 9=true := by decide +kernel
theorem row_checked10 : checkRow 10=true := by decide +kernel
theorem row_checked11 : checkRow 11=true := by decide +kernel
theorem row_checked12 : checkRow 12=true := by decide +kernel
theorem row_checked13 : checkRow 13=true := by decide +kernel
theorem row_checked14 : checkRow 14=true := by decide +kernel
theorem row_checked15 : checkRow 15=true := by decide +kernel
theorem row_checked16 : checkRow 16=true := by decide +kernel
theorem row_checked17 : checkRow 17=true := by decide +kernel
theorem row_checked18 : checkRow 18=true := by decide +kernel
theorem row_checked19 : checkRow 19=true := by decide +kernel
theorem row_checked20 : checkRow 20=true := by decide +kernel
theorem row_checked21 : checkRow 21=true := by decide +kernel
theorem row_checked22 : checkRow 22=true := by decide +kernel
theorem row_checked23 : checkRow 23=true := by decide +kernel
theorem row_checked24 : checkRow 24=true := by decide +kernel
theorem row_checked25 : checkRow 25=true := by decide +kernel
theorem row_checked26 : checkRow 26=true := by decide +kernel
theorem row_checked27 : checkRow 27=true := by decide +kernel
theorem row_checked28 : checkRow 28=true := by decide +kernel
theorem row_checked29 : checkRow 29=true := by decide +kernel
theorem row_checked30 : checkRow 30=true := by decide +kernel
theorem row_checked31 : checkRow 31=true := by decide +kernel
lemma rows_checked (b : Nat) (hb:b<32) : checkRow b=true := by
 interval_cases b
 · exact row_checked00
 · exact row_checked01
 · exact row_checked02
 · exact row_checked03
 · exact row_checked04
 · exact row_checked05
 · exact row_checked06
 · exact row_checked07
 · exact row_checked08
 · exact row_checked09
 · exact row_checked10
 · exact row_checked11
 · exact row_checked12
 · exact row_checked13
 · exact row_checked14
 · exact row_checked15
 · exact row_checked16
 · exact row_checked17
 · exact row_checked18
 · exact row_checked19
 · exact row_checked20
 · exact row_checked21
 · exact row_checked22
 · exact row_checked23
 · exact row_checked24
 · exact row_checked25
 · exact row_checked26
 · exact row_checked27
 · exact row_checked28
 · exact row_checked29
 · exact row_checked30
 · exact row_checked31
lemma all_checked (b c : Nat) (hb:b<32) (hc:c<32) :
 check (512*b+16*c) 8 (wordRow b c) (realRow b c) (imagRow b c)=true ∧ (wordRow b c).length=16 := by
 have h:=(List.all_eq_true.mp (rows_checked b hb)) c (List.mem_range.mpr hc)
 simpa only [Bool.and_eq_true,decide_eq_true_eq] using h
lemma all_raw (b c j : Nat) (hb:b<32) (hc:c<32) (hj:j<16) :
    RHHighFFTArithmeticBase.raw (((wordRow b c)[j]?).getD 0) 8 (512*b+16*c+j)=
      (((((RHHighFFTInputR08.rows[b]?).getD [])[16*c+j]?).getD 0:Int)-2^166,
       ((((RHHighFFTInputI08.rows[b]?).getD [])[16*c+j]?).getD 0:Int)-2^166) := by
  have h:=all_checked b c hb hc
  have hh:=sound (wordRow b c) (realRow b c) (imagRow b c) (512*b+16*c) 8 j (by rw [h.2];exact hj) h.1
  simpa only [realRow,imagRow,List.getElem?_take,List.getElem?_drop,hj,if_true] using hh
end RHHighSequentialFFTAll08
namespace RHHighSequentialFFTAll08
lemma moment_words (b c j q : Nat) (hb:b<32) (hc:c<32) (hj:j<16) (hq:q<26) :
    RHHighFFTArithmeticBase.decode (((wordRow b c)[j]?).getD 0) q=
      RHHighMomentArithmetic.moment (512*b+16*c+j) (RHHighGammaArithmetic.compute (512*b+16*c+j)) q := by
  have h:=TaoFivePrimes.rh_high_height_all_moment_word_arithmetic (512*b+16*c+j) (by omega) q hq
  have h0:(512*b+16*c+j)/512=b:=by omega
  have h1:((512*b+16*c+j)%512)/16=c:=by omega
  have h2:(512*b+16*c+j)%16=j:=by omega
  simpa only [RHHighAllMomentWords.word,h0,h1,h2,RHHighAllMomentWords.blocks,wordRow,blocks] using h

end RHHighSequentialFFTAll08
theorem solution :
  ∀ i : Nat,i<16384 →
  let m:=RHHighMomentArithmetic.moment i (RHHighGammaArithmetic.compute i) 8
  let c:=RHHighFFTArithmeticBase.chirp i
  (m.1*c.1+m.2*c.2,m.2*c.1-m.1*c.2)=
    ((((((RHHighFFTInputR08.rows[i/512]?).getD [])[i%512]?).getD 0:Nat):Int)-2^166,
     (((((RHHighFFTInputI08.rows[i/512]?).getD [])[i%512]?).getD 0:Nat):Int)-2^166) := by
  intro i hi
  let b:=i/512
  let c:=(i%512)/16
  let j:=i%16
  have hb:b<32:=by dsimp [b];omega
  have hc:c<32:=by dsimp [c];omega
  have hj:j<16:=by dsimp [j];omega
  have h:= RHHighSequentialFFTAll08.all_raw b c j hb hc hj
  have hw:=RHHighSequentialFFTAll08.moment_words b c j 8 hb hc hj (by decide)
  unfold RHHighFFTArithmeticBase.raw at h
  rw [hw] at h
  have hi':512*b+16*c+j=i:=by dsimp [b,c,j];omega
  have hcj:16*c+j=i%512:=by dsimp [c,j];omega
  rw [hi',hcj] at h
  exact h
