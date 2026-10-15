-- Prove2me | solution 1 for TaoFivePrimes.rh_high_height_fft_chirp_arithmetic
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T02:26:56.195673+00:00
-- url     : https://prove2.me/submissions/d4347300-c096-4c0a-8a88-a13f660ca8ed

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighFFTArithmeticBase
import Definitions.Def_TaoFivePrimes_RHHighFFTChirpR
import Definitions.Def_TaoFivePrimes_RHHighFFTChirpI
import Definitions.Def_TaoFivePrimes_RHHighFFTChirpS
set_option autoImplicit false
set_option maxHeartbeats 500000
namespace RHHighSequentialChirp
noncomputable def pred (j r v s : Nat) : Prop :=
  let c:=RHHighFFTArithmeticBase.chirp ((j:Int)-16383).natAbs
  (r:Int)=c.1+2^81 ∧ (v:Int)=c.2+2^81 ∧ s=r+v
noncomputable instance predDecidable (j r v s : Nat) : Decidable (pred j r v s) := by unfold pred;infer_instance
noncomputable def check (j : Nat) : List Nat→List Nat→List Nat→Bool
  | [],[],[] => true
  | r::rs,v::vs,s::ss => decide (pred j r v s) && check (j+1) rs vs ss
  | _,_,_ => false
lemma sound (rs vs ss : List Nat) (start j : Nat) (hj:j<rs.length) (h:check start rs vs ss=true) :
    pred (start+j) ((rs[j]?).getD 0) ((vs[j]?).getD 0) ((ss[j]?).getD 0) := by
  induction rs generalizing start j vs ss with
  | nil => simp at hj
  | cons r rs ih =>
    cases vs with
    | nil => simp [check] at h
    | cons v vs => cases ss with
      | nil => simp [check] at h
      | cons s ss =>
        simp only [check,Bool.and_eq_true,decide_eq_true_eq] at h
        cases j with
        | zero => simpa using h.1
        | succ j =>
          have hh:=ih vs ss (start+1) j (by simpa using hj) h.2
          simpa only [List.getElem?_cons_succ,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh
end RHHighSequentialChirp
namespace RHHighFFTChirpRows
open RHHighSequentialChirp
theorem checked00 : check 0 RHHighFFTChirpR.row00 RHHighFFTChirpI.row00 RHHighFFTChirpS.row00=true := by decide +kernel
theorem length00 : RHHighFFTChirpR.row00.length=512 := by decide +kernel
theorem checked01 : check 512 RHHighFFTChirpR.row01 RHHighFFTChirpI.row01 RHHighFFTChirpS.row01=true := by decide +kernel
theorem length01 : RHHighFFTChirpR.row01.length=512 := by decide +kernel
theorem checked02 : check 1024 RHHighFFTChirpR.row02 RHHighFFTChirpI.row02 RHHighFFTChirpS.row02=true := by decide +kernel
theorem length02 : RHHighFFTChirpR.row02.length=512 := by decide +kernel
theorem checked03 : check 1536 RHHighFFTChirpR.row03 RHHighFFTChirpI.row03 RHHighFFTChirpS.row03=true := by decide +kernel
theorem length03 : RHHighFFTChirpR.row03.length=512 := by decide +kernel
theorem checked04 : check 2048 RHHighFFTChirpR.row04 RHHighFFTChirpI.row04 RHHighFFTChirpS.row04=true := by decide +kernel
theorem length04 : RHHighFFTChirpR.row04.length=512 := by decide +kernel
theorem checked05 : check 2560 RHHighFFTChirpR.row05 RHHighFFTChirpI.row05 RHHighFFTChirpS.row05=true := by decide +kernel
theorem length05 : RHHighFFTChirpR.row05.length=512 := by decide +kernel
theorem checked06 : check 3072 RHHighFFTChirpR.row06 RHHighFFTChirpI.row06 RHHighFFTChirpS.row06=true := by decide +kernel
theorem length06 : RHHighFFTChirpR.row06.length=512 := by decide +kernel
theorem checked07 : check 3584 RHHighFFTChirpR.row07 RHHighFFTChirpI.row07 RHHighFFTChirpS.row07=true := by decide +kernel
theorem length07 : RHHighFFTChirpR.row07.length=512 := by decide +kernel
theorem checked08 : check 4096 RHHighFFTChirpR.row08 RHHighFFTChirpI.row08 RHHighFFTChirpS.row08=true := by decide +kernel
theorem length08 : RHHighFFTChirpR.row08.length=512 := by decide +kernel
theorem checked09 : check 4608 RHHighFFTChirpR.row09 RHHighFFTChirpI.row09 RHHighFFTChirpS.row09=true := by decide +kernel
theorem length09 : RHHighFFTChirpR.row09.length=512 := by decide +kernel
theorem checked10 : check 5120 RHHighFFTChirpR.row10 RHHighFFTChirpI.row10 RHHighFFTChirpS.row10=true := by decide +kernel
theorem length10 : RHHighFFTChirpR.row10.length=512 := by decide +kernel
theorem checked11 : check 5632 RHHighFFTChirpR.row11 RHHighFFTChirpI.row11 RHHighFFTChirpS.row11=true := by decide +kernel
theorem length11 : RHHighFFTChirpR.row11.length=512 := by decide +kernel
theorem checked12 : check 6144 RHHighFFTChirpR.row12 RHHighFFTChirpI.row12 RHHighFFTChirpS.row12=true := by decide +kernel
theorem length12 : RHHighFFTChirpR.row12.length=512 := by decide +kernel
theorem checked13 : check 6656 RHHighFFTChirpR.row13 RHHighFFTChirpI.row13 RHHighFFTChirpS.row13=true := by decide +kernel
theorem length13 : RHHighFFTChirpR.row13.length=512 := by decide +kernel
theorem checked14 : check 7168 RHHighFFTChirpR.row14 RHHighFFTChirpI.row14 RHHighFFTChirpS.row14=true := by decide +kernel
theorem length14 : RHHighFFTChirpR.row14.length=512 := by decide +kernel
theorem checked15 : check 7680 RHHighFFTChirpR.row15 RHHighFFTChirpI.row15 RHHighFFTChirpS.row15=true := by decide +kernel
theorem length15 : RHHighFFTChirpR.row15.length=512 := by decide +kernel
theorem checked16 : check 8192 RHHighFFTChirpR.row16 RHHighFFTChirpI.row16 RHHighFFTChirpS.row16=true := by decide +kernel
theorem length16 : RHHighFFTChirpR.row16.length=512 := by decide +kernel
theorem checked17 : check 8704 RHHighFFTChirpR.row17 RHHighFFTChirpI.row17 RHHighFFTChirpS.row17=true := by decide +kernel
theorem length17 : RHHighFFTChirpR.row17.length=512 := by decide +kernel
theorem checked18 : check 9216 RHHighFFTChirpR.row18 RHHighFFTChirpI.row18 RHHighFFTChirpS.row18=true := by decide +kernel
theorem length18 : RHHighFFTChirpR.row18.length=512 := by decide +kernel
theorem checked19 : check 9728 RHHighFFTChirpR.row19 RHHighFFTChirpI.row19 RHHighFFTChirpS.row19=true := by decide +kernel
theorem length19 : RHHighFFTChirpR.row19.length=512 := by decide +kernel
theorem checked20 : check 10240 RHHighFFTChirpR.row20 RHHighFFTChirpI.row20 RHHighFFTChirpS.row20=true := by decide +kernel
theorem length20 : RHHighFFTChirpR.row20.length=512 := by decide +kernel
theorem checked21 : check 10752 RHHighFFTChirpR.row21 RHHighFFTChirpI.row21 RHHighFFTChirpS.row21=true := by decide +kernel
theorem length21 : RHHighFFTChirpR.row21.length=512 := by decide +kernel
theorem checked22 : check 11264 RHHighFFTChirpR.row22 RHHighFFTChirpI.row22 RHHighFFTChirpS.row22=true := by decide +kernel
theorem length22 : RHHighFFTChirpR.row22.length=512 := by decide +kernel
theorem checked23 : check 11776 RHHighFFTChirpR.row23 RHHighFFTChirpI.row23 RHHighFFTChirpS.row23=true := by decide +kernel
theorem length23 : RHHighFFTChirpR.row23.length=512 := by decide +kernel
theorem checked24 : check 12288 RHHighFFTChirpR.row24 RHHighFFTChirpI.row24 RHHighFFTChirpS.row24=true := by decide +kernel
theorem length24 : RHHighFFTChirpR.row24.length=512 := by decide +kernel
theorem checked25 : check 12800 RHHighFFTChirpR.row25 RHHighFFTChirpI.row25 RHHighFFTChirpS.row25=true := by decide +kernel
theorem length25 : RHHighFFTChirpR.row25.length=512 := by decide +kernel
theorem checked26 : check 13312 RHHighFFTChirpR.row26 RHHighFFTChirpI.row26 RHHighFFTChirpS.row26=true := by decide +kernel
theorem length26 : RHHighFFTChirpR.row26.length=512 := by decide +kernel
theorem checked27 : check 13824 RHHighFFTChirpR.row27 RHHighFFTChirpI.row27 RHHighFFTChirpS.row27=true := by decide +kernel
theorem length27 : RHHighFFTChirpR.row27.length=512 := by decide +kernel
theorem checked28 : check 14336 RHHighFFTChirpR.row28 RHHighFFTChirpI.row28 RHHighFFTChirpS.row28=true := by decide +kernel
theorem length28 : RHHighFFTChirpR.row28.length=512 := by decide +kernel
theorem checked29 : check 14848 RHHighFFTChirpR.row29 RHHighFFTChirpI.row29 RHHighFFTChirpS.row29=true := by decide +kernel
theorem length29 : RHHighFFTChirpR.row29.length=512 := by decide +kernel
theorem checked30 : check 15360 RHHighFFTChirpR.row30 RHHighFFTChirpI.row30 RHHighFFTChirpS.row30=true := by decide +kernel
theorem length30 : RHHighFFTChirpR.row30.length=512 := by decide +kernel
theorem checked31 : check 15872 RHHighFFTChirpR.row31 RHHighFFTChirpI.row31 RHHighFFTChirpS.row31=true := by decide +kernel
theorem length31 : RHHighFFTChirpR.row31.length=512 := by decide +kernel
theorem checked32 : check 16384 RHHighFFTChirpR.row32 RHHighFFTChirpI.row32 RHHighFFTChirpS.row32=true := by decide +kernel
theorem length32 : RHHighFFTChirpR.row32.length=512 := by decide +kernel
theorem checked33 : check 16896 RHHighFFTChirpR.row33 RHHighFFTChirpI.row33 RHHighFFTChirpS.row33=true := by decide +kernel
theorem length33 : RHHighFFTChirpR.row33.length=512 := by decide +kernel
theorem checked34 : check 17408 RHHighFFTChirpR.row34 RHHighFFTChirpI.row34 RHHighFFTChirpS.row34=true := by decide +kernel
theorem length34 : RHHighFFTChirpR.row34.length=512 := by decide +kernel
theorem checked35 : check 17920 RHHighFFTChirpR.row35 RHHighFFTChirpI.row35 RHHighFFTChirpS.row35=true := by decide +kernel
theorem length35 : RHHighFFTChirpR.row35.length=512 := by decide +kernel
theorem checked36 : check 18432 RHHighFFTChirpR.row36 RHHighFFTChirpI.row36 RHHighFFTChirpS.row36=true := by decide +kernel
theorem length36 : RHHighFFTChirpR.row36.length=512 := by decide +kernel
theorem checked37 : check 18944 RHHighFFTChirpR.row37 RHHighFFTChirpI.row37 RHHighFFTChirpS.row37=true := by decide +kernel
theorem length37 : RHHighFFTChirpR.row37.length=512 := by decide +kernel
theorem checked38 : check 19456 RHHighFFTChirpR.row38 RHHighFFTChirpI.row38 RHHighFFTChirpS.row38=true := by decide +kernel
theorem length38 : RHHighFFTChirpR.row38.length=512 := by decide +kernel
theorem checked39 : check 19968 RHHighFFTChirpR.row39 RHHighFFTChirpI.row39 RHHighFFTChirpS.row39=true := by decide +kernel
theorem length39 : RHHighFFTChirpR.row39.length=512 := by decide +kernel
theorem checked40 : check 20480 RHHighFFTChirpR.row40 RHHighFFTChirpI.row40 RHHighFFTChirpS.row40=true := by decide +kernel
theorem length40 : RHHighFFTChirpR.row40.length=512 := by decide +kernel
theorem checked41 : check 20992 RHHighFFTChirpR.row41 RHHighFFTChirpI.row41 RHHighFFTChirpS.row41=true := by decide +kernel
theorem length41 : RHHighFFTChirpR.row41.length=512 := by decide +kernel
theorem checked42 : check 21504 RHHighFFTChirpR.row42 RHHighFFTChirpI.row42 RHHighFFTChirpS.row42=true := by decide +kernel
theorem length42 : RHHighFFTChirpR.row42.length=512 := by decide +kernel
theorem checked43 : check 22016 RHHighFFTChirpR.row43 RHHighFFTChirpI.row43 RHHighFFTChirpS.row43=true := by decide +kernel
theorem length43 : RHHighFFTChirpR.row43.length=512 := by decide +kernel
theorem checked44 : check 22528 RHHighFFTChirpR.row44 RHHighFFTChirpI.row44 RHHighFFTChirpS.row44=true := by decide +kernel
theorem length44 : RHHighFFTChirpR.row44.length=512 := by decide +kernel
theorem checked45 : check 23040 RHHighFFTChirpR.row45 RHHighFFTChirpI.row45 RHHighFFTChirpS.row45=true := by decide +kernel
theorem length45 : RHHighFFTChirpR.row45.length=512 := by decide +kernel
theorem checked46 : check 23552 RHHighFFTChirpR.row46 RHHighFFTChirpI.row46 RHHighFFTChirpS.row46=true := by decide +kernel
theorem length46 : RHHighFFTChirpR.row46.length=512 := by decide +kernel
theorem checked47 : check 24064 RHHighFFTChirpR.row47 RHHighFFTChirpI.row47 RHHighFFTChirpS.row47=true := by decide +kernel
theorem length47 : RHHighFFTChirpR.row47.length=512 := by decide +kernel
theorem checked48 : check 24576 RHHighFFTChirpR.row48 RHHighFFTChirpI.row48 RHHighFFTChirpS.row48=true := by decide +kernel
theorem length48 : RHHighFFTChirpR.row48.length=512 := by decide +kernel
theorem checked49 : check 25088 RHHighFFTChirpR.row49 RHHighFFTChirpI.row49 RHHighFFTChirpS.row49=true := by decide +kernel
theorem length49 : RHHighFFTChirpR.row49.length=512 := by decide +kernel
theorem checked50 : check 25600 RHHighFFTChirpR.row50 RHHighFFTChirpI.row50 RHHighFFTChirpS.row50=true := by decide +kernel
theorem length50 : RHHighFFTChirpR.row50.length=512 := by decide +kernel
theorem checked51 : check 26112 RHHighFFTChirpR.row51 RHHighFFTChirpI.row51 RHHighFFTChirpS.row51=true := by decide +kernel
theorem length51 : RHHighFFTChirpR.row51.length=512 := by decide +kernel
theorem checked52 : check 26624 RHHighFFTChirpR.row52 RHHighFFTChirpI.row52 RHHighFFTChirpS.row52=true := by decide +kernel
theorem length52 : RHHighFFTChirpR.row52.length=512 := by decide +kernel
theorem checked53 : check 27136 RHHighFFTChirpR.row53 RHHighFFTChirpI.row53 RHHighFFTChirpS.row53=true := by decide +kernel
theorem length53 : RHHighFFTChirpR.row53.length=512 := by decide +kernel
theorem checked54 : check 27648 RHHighFFTChirpR.row54 RHHighFFTChirpI.row54 RHHighFFTChirpS.row54=true := by decide +kernel
theorem length54 : RHHighFFTChirpR.row54.length=512 := by decide +kernel
theorem checked55 : check 28160 RHHighFFTChirpR.row55 RHHighFFTChirpI.row55 RHHighFFTChirpS.row55=true := by decide +kernel
theorem length55 : RHHighFFTChirpR.row55.length=512 := by decide +kernel
theorem checked56 : check 28672 RHHighFFTChirpR.row56 RHHighFFTChirpI.row56 RHHighFFTChirpS.row56=true := by decide +kernel
theorem length56 : RHHighFFTChirpR.row56.length=512 := by decide +kernel
theorem checked57 : check 29184 RHHighFFTChirpR.row57 RHHighFFTChirpI.row57 RHHighFFTChirpS.row57=true := by decide +kernel
theorem length57 : RHHighFFTChirpR.row57.length=512 := by decide +kernel
theorem checked58 : check 29696 RHHighFFTChirpR.row58 RHHighFFTChirpI.row58 RHHighFFTChirpS.row58=true := by decide +kernel
theorem length58 : RHHighFFTChirpR.row58.length=512 := by decide +kernel
theorem checked59 : check 30208 RHHighFFTChirpR.row59 RHHighFFTChirpI.row59 RHHighFFTChirpS.row59=true := by decide +kernel
theorem length59 : RHHighFFTChirpR.row59.length=512 := by decide +kernel
theorem checked60 : check 30720 RHHighFFTChirpR.row60 RHHighFFTChirpI.row60 RHHighFFTChirpS.row60=true := by decide +kernel
theorem length60 : RHHighFFTChirpR.row60.length=512 := by decide +kernel
theorem checked61 : check 31232 RHHighFFTChirpR.row61 RHHighFFTChirpI.row61 RHHighFFTChirpS.row61=true := by decide +kernel
theorem length61 : RHHighFFTChirpR.row61.length=512 := by decide +kernel
theorem checked62 : check 31744 RHHighFFTChirpR.row62 RHHighFFTChirpI.row62 RHHighFFTChirpS.row62=true := by decide +kernel
theorem length62 : RHHighFFTChirpR.row62.length=512 := by decide +kernel
theorem checked63 : check 32256 RHHighFFTChirpR.row63 RHHighFFTChirpI.row63 RHHighFFTChirpS.row63=true := by decide +kernel
theorem length63 : RHHighFFTChirpR.row63.length=511 := by decide +kernel
end RHHighFFTChirpRows
theorem solution :
  ∀ c : Nat, c<64 → ∀ j : Nat, j < min 512 (32767-512*c) →
  (let v:=RHHighFFTArithmeticBase.chirp ((512*c+j:Int)-16383).natAbs
   let r:Nat:=(((((RHHighFFTChirpR.rows[c]?).getD [])[j]?).getD 0))
   let i:Nat:=(((((RHHighFFTChirpI.rows[c]?).getD [])[j]?).getD 0))
   let s:Nat:=(((((RHHighFFTChirpS.rows[c]?).getD [])[j]?).getD 0))
   (r:Int)=v.1+2^81 ∧ (i:Int)=v.2+2^81 ∧ s=r+i) := by
  intro c hc j hj
  change RHHighSequentialChirp.pred (512*c+j) (((((RHHighFFTChirpR.rows[c]?).getD [])[j]?).getD 0)) (((((RHHighFFTChirpI.rows[c]?).getD [])[j]?).getD 0)) (((((RHHighFFTChirpS.rows[c]?).getD [])[j]?).getD 0)) 
  interval_cases c
  · have h:=RHHighSequentialChirp.sound RHHighFFTChirpR.row00 RHHighFFTChirpI.row00 RHHighFFTChirpS.row00 0 j
      (by rw [RHHighFFTChirpRows.length00];norm_num at hj;exact hj) RHHighFFTChirpRows.checked00
    simpa only [RHHighFFTChirpR.rows,RHHighFFTChirpI.rows,RHHighFFTChirpS.rows,
      List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,Nat.reduceMul] using h
  · have h:=RHHighSequentialChirp.sound RHHighFFTChirpR.row01 RHHighFFTChirpI.row01 RHHighFFTChirpS.row01 512 j
      (by rw [RHHighFFTChirpRows.length01];norm_num at hj;exact hj) RHHighFFTChirpRows.checked01
    simpa only [RHHighFFTChirpR.rows,RHHighFFTChirpI.rows,RHHighFFTChirpS.rows,
      List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,Nat.reduceMul] using h
  · have h:=RHHighSequentialChirp.sound RHHighFFTChirpR.row02 RHHighFFTChirpI.row02 RHHighFFTChirpS.row02 1024 j
      (by rw [RHHighFFTChirpRows.length02];norm_num at hj;exact hj) RHHighFFTChirpRows.checked02
    simpa only [RHHighFFTChirpR.rows,RHHighFFTChirpI.rows,RHHighFFTChirpS.rows,
      List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,Nat.reduceMul] using h
  · have h:=RHHighSequentialChirp.sound RHHighFFTChirpR.row03 RHHighFFTChirpI.row03 RHHighFFTChirpS.row03 1536 j
      (by rw [RHHighFFTChirpRows.length03];norm_num at hj;exact hj) RHHighFFTChirpRows.checked03
    simpa only [RHHighFFTChirpR.rows,RHHighFFTChirpI.rows,RHHighFFTChirpS.rows,
      List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,Nat.reduceMul] using h
  · have h:=RHHighSequentialChirp.sound RHHighFFTChirpR.row04 RHHighFFTChirpI.row04 RHHighFFTChirpS.row04 2048 j
      (by rw [RHHighFFTChirpRows.length04];norm_num at hj;exact hj) RHHighFFTChirpRows.checked04
    simpa only [RHHighFFTChirpR.rows,RHHighFFTChirpI.rows,RHHighFFTChirpS.rows,
      List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,Nat.reduceMul] using h
  · have h:=RHHighSequentialChirp.sound RHHighFFTChirpR.row05 RHHighFFTChirpI.row05 RHHighFFTChirpS.row05 2560 j
      (by rw [RHHighFFTChirpRows.length05];norm_num at hj;exact hj) RHHighFFTChirpRows.checked05
    simpa only [RHHighFFTChirpR.rows,RHHighFFTChirpI.rows,RHHighFFTChirpS.rows,
      List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,Nat.reduceMul] using h
  · have h:=RHHighSequentialChirp.sound RHHighFFTChirpR.row06 RHHighFFTChirpI.row06 RHHighFFTChirpS.row06 3072 j
      (by rw [RHHighFFTChirpRows.length06];norm_num at hj;exact hj) RHHighFFTChirpRows.checked06
    simpa only [RHHighFFTChirpR.rows,RHHighFFTChirpI.rows,RHHighFFTChirpS.rows,
      List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,Nat.reduceMul] using h
  · have h:=RHHighSequentialChirp.sound RHHighFFTChirpR.row07 RHHighFFTChirpI.row07 RHHighFFTChirpS.row07 3584 j
      (by rw [RHHighFFTChirpRows.length07];norm_num at hj;exact hj) RHHighFFTChirpRows.checked07
    simpa only [RHHighFFTChirpR.rows,RHHighFFTChirpI.rows,RHHighFFTChirpS.rows,
      List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,Nat.reduceMul] using h
  · have h:=RHHighSequentialChirp.sound RHHighFFTChirpR.row08 RHHighFFTChirpI.row08 RHHighFFTChirpS.row08 4096 j
      (by rw [RHHighFFTChirpRows.length08];norm_num at hj;exact hj) RHHighFFTChirpRows.checked08
    simpa only [RHHighFFTChirpR.rows,RHHighFFTChirpI.rows,RHHighFFTChirpS.rows,
      List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,Nat.reduceMul] using h
  · have h:=RHHighSequentialChirp.sound RHHighFFTChirpR.row09 RHHighFFTChirpI.row09 RHHighFFTChirpS.row09 4608 j
      (by rw [RHHighFFTChirpRows.length09];norm_num at hj;exact hj) RHHighFFTChirpRows.checked09
    simpa only [RHHighFFTChirpR.rows,RHHighFFTChirpI.rows,RHHighFFTChirpS.rows,
      List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,Nat.reduceMul] using h
  · have h:=RHHighSequentialChirp.sound RHHighFFTChirpR.row10 RHHighFFTChirpI.row10 RHHighFFTChirpS.row10 5120 j
      (by rw [RHHighFFTChirpRows.length10];norm_num at hj;exact hj) RHHighFFTChirpRows.checked10
    simpa only [RHHighFFTChirpR.rows,RHHighFFTChirpI.rows,RHHighFFTChirpS.rows,
      List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,Nat.reduceMul] using h
  · have h:=RHHighSequentialChirp.sound RHHighFFTChirpR.row11 RHHighFFTChirpI.row11 RHHighFFTChirpS.row11 5632 j
      (by rw [RHHighFFTChirpRows.length11];norm_num at hj;exact hj) RHHighFFTChirpRows.checked11
    simpa only [RHHighFFTChirpR.rows,RHHighFFTChirpI.rows,RHHighFFTChirpS.rows,
      List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,Nat.reduceMul] using h
  · have h:=RHHighSequentialChirp.sound RHHighFFTChirpR.row12 RHHighFFTChirpI.row12 RHHighFFTChirpS.row12 6144 j
      (by rw [RHHighFFTChirpRows.length12];norm_num at hj;exact hj) RHHighFFTChirpRows.checked12
    simpa only [RHHighFFTChirpR.rows,RHHighFFTChirpI.rows,RHHighFFTChirpS.rows,
      List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,Nat.reduceMul] using h
  · have h:=RHHighSequentialChirp.sound RHHighFFTChirpR.row13 RHHighFFTChirpI.row13 RHHighFFTChirpS.row13 6656 j
      (by rw [RHHighFFTChirpRows.length13];norm_num at hj;exact hj) RHHighFFTChirpRows.checked13
    simpa only [RHHighFFTChirpR.rows,RHHighFFTChirpI.rows,RHHighFFTChirpS.rows,
      List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,Nat.reduceMul] using h
  · have h:=RHHighSequentialChirp.sound RHHighFFTChirpR.row14 RHHighFFTChirpI.row14 RHHighFFTChirpS.row14 7168 j
      (by rw [RHHighFFTChirpRows.length14];norm_num at hj;exact hj) RHHighFFTChirpRows.checked14
    simpa only [RHHighFFTChirpR.rows,RHHighFFTChirpI.rows,RHHighFFTChirpS.rows,
      List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,Nat.reduceMul] using h
  · have h:=RHHighSequentialChirp.sound RHHighFFTChirpR.row15 RHHighFFTChirpI.row15 RHHighFFTChirpS.row15 7680 j
      (by rw [RHHighFFTChirpRows.length15];norm_num at hj;exact hj) RHHighFFTChirpRows.checked15
    simpa only [RHHighFFTChirpR.rows,RHHighFFTChirpI.rows,RHHighFFTChirpS.rows,
      List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,Nat.reduceMul] using h
  · have h:=RHHighSequentialChirp.sound RHHighFFTChirpR.row16 RHHighFFTChirpI.row16 RHHighFFTChirpS.row16 8192 j
      (by rw [RHHighFFTChirpRows.length16];norm_num at hj;exact hj) RHHighFFTChirpRows.checked16
    simpa only [RHHighFFTChirpR.rows,RHHighFFTChirpI.rows,RHHighFFTChirpS.rows,
      List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,Nat.reduceMul] using h
  · have h:=RHHighSequentialChirp.sound RHHighFFTChirpR.row17 RHHighFFTChirpI.row17 RHHighFFTChirpS.row17 8704 j
      (by rw [RHHighFFTChirpRows.length17];norm_num at hj;exact hj) RHHighFFTChirpRows.checked17
    simpa only [RHHighFFTChirpR.rows,RHHighFFTChirpI.rows,RHHighFFTChirpS.rows,
      List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,Nat.reduceMul] using h
  · have h:=RHHighSequentialChirp.sound RHHighFFTChirpR.row18 RHHighFFTChirpI.row18 RHHighFFTChirpS.row18 9216 j
      (by rw [RHHighFFTChirpRows.length18];norm_num at hj;exact hj) RHHighFFTChirpRows.checked18
    simpa only [RHHighFFTChirpR.rows,RHHighFFTChirpI.rows,RHHighFFTChirpS.rows,
      List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,Nat.reduceMul] using h
  · have h:=RHHighSequentialChirp.sound RHHighFFTChirpR.row19 RHHighFFTChirpI.row19 RHHighFFTChirpS.row19 9728 j
      (by rw [RHHighFFTChirpRows.length19];norm_num at hj;exact hj) RHHighFFTChirpRows.checked19
    simpa only [RHHighFFTChirpR.rows,RHHighFFTChirpI.rows,RHHighFFTChirpS.rows,
      List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,Nat.reduceMul] using h
  · have h:=RHHighSequentialChirp.sound RHHighFFTChirpR.row20 RHHighFFTChirpI.row20 RHHighFFTChirpS.row20 10240 j
      (by rw [RHHighFFTChirpRows.length20];norm_num at hj;exact hj) RHHighFFTChirpRows.checked20
    simpa only [RHHighFFTChirpR.rows,RHHighFFTChirpI.rows,RHHighFFTChirpS.rows,
      List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,Nat.reduceMul] using h
  · have h:=RHHighSequentialChirp.sound RHHighFFTChirpR.row21 RHHighFFTChirpI.row21 RHHighFFTChirpS.row21 10752 j
      (by rw [RHHighFFTChirpRows.length21];norm_num at hj;exact hj) RHHighFFTChirpRows.checked21
    simpa only [RHHighFFTChirpR.rows,RHHighFFTChirpI.rows,RHHighFFTChirpS.rows,
      List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,Nat.reduceMul] using h
  · have h:=RHHighSequentialChirp.sound RHHighFFTChirpR.row22 RHHighFFTChirpI.row22 RHHighFFTChirpS.row22 11264 j
      (by rw [RHHighFFTChirpRows.length22];norm_num at hj;exact hj) RHHighFFTChirpRows.checked22
    simpa only [RHHighFFTChirpR.rows,RHHighFFTChirpI.rows,RHHighFFTChirpS.rows,
      List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,Nat.reduceMul] using h
  · have h:=RHHighSequentialChirp.sound RHHighFFTChirpR.row23 RHHighFFTChirpI.row23 RHHighFFTChirpS.row23 11776 j
      (by rw [RHHighFFTChirpRows.length23];norm_num at hj;exact hj) RHHighFFTChirpRows.checked23
    simpa only [RHHighFFTChirpR.rows,RHHighFFTChirpI.rows,RHHighFFTChirpS.rows,
      List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,Nat.reduceMul] using h
  · have h:=RHHighSequentialChirp.sound RHHighFFTChirpR.row24 RHHighFFTChirpI.row24 RHHighFFTChirpS.row24 12288 j
      (by rw [RHHighFFTChirpRows.length24];norm_num at hj;exact hj) RHHighFFTChirpRows.checked24
    simpa only [RHHighFFTChirpR.rows,RHHighFFTChirpI.rows,RHHighFFTChirpS.rows,
      List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,Nat.reduceMul] using h
  · have h:=RHHighSequentialChirp.sound RHHighFFTChirpR.row25 RHHighFFTChirpI.row25 RHHighFFTChirpS.row25 12800 j
      (by rw [RHHighFFTChirpRows.length25];norm_num at hj;exact hj) RHHighFFTChirpRows.checked25
    simpa only [RHHighFFTChirpR.rows,RHHighFFTChirpI.rows,RHHighFFTChirpS.rows,
      List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,Nat.reduceMul] using h
  · have h:=RHHighSequentialChirp.sound RHHighFFTChirpR.row26 RHHighFFTChirpI.row26 RHHighFFTChirpS.row26 13312 j
      (by rw [RHHighFFTChirpRows.length26];norm_num at hj;exact hj) RHHighFFTChirpRows.checked26
    simpa only [RHHighFFTChirpR.rows,RHHighFFTChirpI.rows,RHHighFFTChirpS.rows,
      List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,Nat.reduceMul] using h
  · have h:=RHHighSequentialChirp.sound RHHighFFTChirpR.row27 RHHighFFTChirpI.row27 RHHighFFTChirpS.row27 13824 j
      (by rw [RHHighFFTChirpRows.length27];norm_num at hj;exact hj) RHHighFFTChirpRows.checked27
    simpa only [RHHighFFTChirpR.rows,RHHighFFTChirpI.rows,RHHighFFTChirpS.rows,
      List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,Nat.reduceMul] using h
  · have h:=RHHighSequentialChirp.sound RHHighFFTChirpR.row28 RHHighFFTChirpI.row28 RHHighFFTChirpS.row28 14336 j
      (by rw [RHHighFFTChirpRows.length28];norm_num at hj;exact hj) RHHighFFTChirpRows.checked28
    simpa only [RHHighFFTChirpR.rows,RHHighFFTChirpI.rows,RHHighFFTChirpS.rows,
      List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,Nat.reduceMul] using h
  · have h:=RHHighSequentialChirp.sound RHHighFFTChirpR.row29 RHHighFFTChirpI.row29 RHHighFFTChirpS.row29 14848 j
      (by rw [RHHighFFTChirpRows.length29];norm_num at hj;exact hj) RHHighFFTChirpRows.checked29
    simpa only [RHHighFFTChirpR.rows,RHHighFFTChirpI.rows,RHHighFFTChirpS.rows,
      List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,Nat.reduceMul] using h
  · have h:=RHHighSequentialChirp.sound RHHighFFTChirpR.row30 RHHighFFTChirpI.row30 RHHighFFTChirpS.row30 15360 j
      (by rw [RHHighFFTChirpRows.length30];norm_num at hj;exact hj) RHHighFFTChirpRows.checked30
    simpa only [RHHighFFTChirpR.rows,RHHighFFTChirpI.rows,RHHighFFTChirpS.rows,
      List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,Nat.reduceMul] using h
  · have h:=RHHighSequentialChirp.sound RHHighFFTChirpR.row31 RHHighFFTChirpI.row31 RHHighFFTChirpS.row31 15872 j
      (by rw [RHHighFFTChirpRows.length31];norm_num at hj;exact hj) RHHighFFTChirpRows.checked31
    simpa only [RHHighFFTChirpR.rows,RHHighFFTChirpI.rows,RHHighFFTChirpS.rows,
      List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,Nat.reduceMul] using h
  · have h:=RHHighSequentialChirp.sound RHHighFFTChirpR.row32 RHHighFFTChirpI.row32 RHHighFFTChirpS.row32 16384 j
      (by rw [RHHighFFTChirpRows.length32];norm_num at hj;exact hj) RHHighFFTChirpRows.checked32
    simpa only [RHHighFFTChirpR.rows,RHHighFFTChirpI.rows,RHHighFFTChirpS.rows,
      List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,Nat.reduceMul] using h
  · have h:=RHHighSequentialChirp.sound RHHighFFTChirpR.row33 RHHighFFTChirpI.row33 RHHighFFTChirpS.row33 16896 j
      (by rw [RHHighFFTChirpRows.length33];norm_num at hj;exact hj) RHHighFFTChirpRows.checked33
    simpa only [RHHighFFTChirpR.rows,RHHighFFTChirpI.rows,RHHighFFTChirpS.rows,
      List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,Nat.reduceMul] using h
  · have h:=RHHighSequentialChirp.sound RHHighFFTChirpR.row34 RHHighFFTChirpI.row34 RHHighFFTChirpS.row34 17408 j
      (by rw [RHHighFFTChirpRows.length34];norm_num at hj;exact hj) RHHighFFTChirpRows.checked34
    simpa only [RHHighFFTChirpR.rows,RHHighFFTChirpI.rows,RHHighFFTChirpS.rows,
      List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,Nat.reduceMul] using h
  · have h:=RHHighSequentialChirp.sound RHHighFFTChirpR.row35 RHHighFFTChirpI.row35 RHHighFFTChirpS.row35 17920 j
      (by rw [RHHighFFTChirpRows.length35];norm_num at hj;exact hj) RHHighFFTChirpRows.checked35
    simpa only [RHHighFFTChirpR.rows,RHHighFFTChirpI.rows,RHHighFFTChirpS.rows,
      List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,Nat.reduceMul] using h
  · have h:=RHHighSequentialChirp.sound RHHighFFTChirpR.row36 RHHighFFTChirpI.row36 RHHighFFTChirpS.row36 18432 j
      (by rw [RHHighFFTChirpRows.length36];norm_num at hj;exact hj) RHHighFFTChirpRows.checked36
    simpa only [RHHighFFTChirpR.rows,RHHighFFTChirpI.rows,RHHighFFTChirpS.rows,
      List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,Nat.reduceMul] using h
  · have h:=RHHighSequentialChirp.sound RHHighFFTChirpR.row37 RHHighFFTChirpI.row37 RHHighFFTChirpS.row37 18944 j
      (by rw [RHHighFFTChirpRows.length37];norm_num at hj;exact hj) RHHighFFTChirpRows.checked37
    simpa only [RHHighFFTChirpR.rows,RHHighFFTChirpI.rows,RHHighFFTChirpS.rows,
      List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,Nat.reduceMul] using h
  · have h:=RHHighSequentialChirp.sound RHHighFFTChirpR.row38 RHHighFFTChirpI.row38 RHHighFFTChirpS.row38 19456 j
      (by rw [RHHighFFTChirpRows.length38];norm_num at hj;exact hj) RHHighFFTChirpRows.checked38
    simpa only [RHHighFFTChirpR.rows,RHHighFFTChirpI.rows,RHHighFFTChirpS.rows,
      List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,Nat.reduceMul] using h
  · have h:=RHHighSequentialChirp.sound RHHighFFTChirpR.row39 RHHighFFTChirpI.row39 RHHighFFTChirpS.row39 19968 j
      (by rw [RHHighFFTChirpRows.length39];norm_num at hj;exact hj) RHHighFFTChirpRows.checked39
    simpa only [RHHighFFTChirpR.rows,RHHighFFTChirpI.rows,RHHighFFTChirpS.rows,
      List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,Nat.reduceMul] using h
  · have h:=RHHighSequentialChirp.sound RHHighFFTChirpR.row40 RHHighFFTChirpI.row40 RHHighFFTChirpS.row40 20480 j
      (by rw [RHHighFFTChirpRows.length40];norm_num at hj;exact hj) RHHighFFTChirpRows.checked40
    simpa only [RHHighFFTChirpR.rows,RHHighFFTChirpI.rows,RHHighFFTChirpS.rows,
      List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,Nat.reduceMul] using h
  · have h:=RHHighSequentialChirp.sound RHHighFFTChirpR.row41 RHHighFFTChirpI.row41 RHHighFFTChirpS.row41 20992 j
      (by rw [RHHighFFTChirpRows.length41];norm_num at hj;exact hj) RHHighFFTChirpRows.checked41
    simpa only [RHHighFFTChirpR.rows,RHHighFFTChirpI.rows,RHHighFFTChirpS.rows,
      List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,Nat.reduceMul] using h
  · have h:=RHHighSequentialChirp.sound RHHighFFTChirpR.row42 RHHighFFTChirpI.row42 RHHighFFTChirpS.row42 21504 j
      (by rw [RHHighFFTChirpRows.length42];norm_num at hj;exact hj) RHHighFFTChirpRows.checked42
    simpa only [RHHighFFTChirpR.rows,RHHighFFTChirpI.rows,RHHighFFTChirpS.rows,
      List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,Nat.reduceMul] using h
  · have h:=RHHighSequentialChirp.sound RHHighFFTChirpR.row43 RHHighFFTChirpI.row43 RHHighFFTChirpS.row43 22016 j
      (by rw [RHHighFFTChirpRows.length43];norm_num at hj;exact hj) RHHighFFTChirpRows.checked43
    simpa only [RHHighFFTChirpR.rows,RHHighFFTChirpI.rows,RHHighFFTChirpS.rows,
      List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,Nat.reduceMul] using h
  · have h:=RHHighSequentialChirp.sound RHHighFFTChirpR.row44 RHHighFFTChirpI.row44 RHHighFFTChirpS.row44 22528 j
      (by rw [RHHighFFTChirpRows.length44];norm_num at hj;exact hj) RHHighFFTChirpRows.checked44
    simpa only [RHHighFFTChirpR.rows,RHHighFFTChirpI.rows,RHHighFFTChirpS.rows,
      List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,Nat.reduceMul] using h
  · have h:=RHHighSequentialChirp.sound RHHighFFTChirpR.row45 RHHighFFTChirpI.row45 RHHighFFTChirpS.row45 23040 j
      (by rw [RHHighFFTChirpRows.length45];norm_num at hj;exact hj) RHHighFFTChirpRows.checked45
    simpa only [RHHighFFTChirpR.rows,RHHighFFTChirpI.rows,RHHighFFTChirpS.rows,
      List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,Nat.reduceMul] using h
  · have h:=RHHighSequentialChirp.sound RHHighFFTChirpR.row46 RHHighFFTChirpI.row46 RHHighFFTChirpS.row46 23552 j
      (by rw [RHHighFFTChirpRows.length46];norm_num at hj;exact hj) RHHighFFTChirpRows.checked46
    simpa only [RHHighFFTChirpR.rows,RHHighFFTChirpI.rows,RHHighFFTChirpS.rows,
      List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,Nat.reduceMul] using h
  · have h:=RHHighSequentialChirp.sound RHHighFFTChirpR.row47 RHHighFFTChirpI.row47 RHHighFFTChirpS.row47 24064 j
      (by rw [RHHighFFTChirpRows.length47];norm_num at hj;exact hj) RHHighFFTChirpRows.checked47
    simpa only [RHHighFFTChirpR.rows,RHHighFFTChirpI.rows,RHHighFFTChirpS.rows,
      List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,Nat.reduceMul] using h
  · have h:=RHHighSequentialChirp.sound RHHighFFTChirpR.row48 RHHighFFTChirpI.row48 RHHighFFTChirpS.row48 24576 j
      (by rw [RHHighFFTChirpRows.length48];norm_num at hj;exact hj) RHHighFFTChirpRows.checked48
    simpa only [RHHighFFTChirpR.rows,RHHighFFTChirpI.rows,RHHighFFTChirpS.rows,
      List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,Nat.reduceMul] using h
  · have h:=RHHighSequentialChirp.sound RHHighFFTChirpR.row49 RHHighFFTChirpI.row49 RHHighFFTChirpS.row49 25088 j
      (by rw [RHHighFFTChirpRows.length49];norm_num at hj;exact hj) RHHighFFTChirpRows.checked49
    simpa only [RHHighFFTChirpR.rows,RHHighFFTChirpI.rows,RHHighFFTChirpS.rows,
      List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,Nat.reduceMul] using h
  · have h:=RHHighSequentialChirp.sound RHHighFFTChirpR.row50 RHHighFFTChirpI.row50 RHHighFFTChirpS.row50 25600 j
      (by rw [RHHighFFTChirpRows.length50];norm_num at hj;exact hj) RHHighFFTChirpRows.checked50
    simpa only [RHHighFFTChirpR.rows,RHHighFFTChirpI.rows,RHHighFFTChirpS.rows,
      List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,Nat.reduceMul] using h
  · have h:=RHHighSequentialChirp.sound RHHighFFTChirpR.row51 RHHighFFTChirpI.row51 RHHighFFTChirpS.row51 26112 j
      (by rw [RHHighFFTChirpRows.length51];norm_num at hj;exact hj) RHHighFFTChirpRows.checked51
    simpa only [RHHighFFTChirpR.rows,RHHighFFTChirpI.rows,RHHighFFTChirpS.rows,
      List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,Nat.reduceMul] using h
  · have h:=RHHighSequentialChirp.sound RHHighFFTChirpR.row52 RHHighFFTChirpI.row52 RHHighFFTChirpS.row52 26624 j
      (by rw [RHHighFFTChirpRows.length52];norm_num at hj;exact hj) RHHighFFTChirpRows.checked52
    simpa only [RHHighFFTChirpR.rows,RHHighFFTChirpI.rows,RHHighFFTChirpS.rows,
      List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,Nat.reduceMul] using h
  · have h:=RHHighSequentialChirp.sound RHHighFFTChirpR.row53 RHHighFFTChirpI.row53 RHHighFFTChirpS.row53 27136 j
      (by rw [RHHighFFTChirpRows.length53];norm_num at hj;exact hj) RHHighFFTChirpRows.checked53
    simpa only [RHHighFFTChirpR.rows,RHHighFFTChirpI.rows,RHHighFFTChirpS.rows,
      List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,Nat.reduceMul] using h
  · have h:=RHHighSequentialChirp.sound RHHighFFTChirpR.row54 RHHighFFTChirpI.row54 RHHighFFTChirpS.row54 27648 j
      (by rw [RHHighFFTChirpRows.length54];norm_num at hj;exact hj) RHHighFFTChirpRows.checked54
    simpa only [RHHighFFTChirpR.rows,RHHighFFTChirpI.rows,RHHighFFTChirpS.rows,
      List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,Nat.reduceMul] using h
  · have h:=RHHighSequentialChirp.sound RHHighFFTChirpR.row55 RHHighFFTChirpI.row55 RHHighFFTChirpS.row55 28160 j
      (by rw [RHHighFFTChirpRows.length55];norm_num at hj;exact hj) RHHighFFTChirpRows.checked55
    simpa only [RHHighFFTChirpR.rows,RHHighFFTChirpI.rows,RHHighFFTChirpS.rows,
      List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,Nat.reduceMul] using h
  · have h:=RHHighSequentialChirp.sound RHHighFFTChirpR.row56 RHHighFFTChirpI.row56 RHHighFFTChirpS.row56 28672 j
      (by rw [RHHighFFTChirpRows.length56];norm_num at hj;exact hj) RHHighFFTChirpRows.checked56
    simpa only [RHHighFFTChirpR.rows,RHHighFFTChirpI.rows,RHHighFFTChirpS.rows,
      List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,Nat.reduceMul] using h
  · have h:=RHHighSequentialChirp.sound RHHighFFTChirpR.row57 RHHighFFTChirpI.row57 RHHighFFTChirpS.row57 29184 j
      (by rw [RHHighFFTChirpRows.length57];norm_num at hj;exact hj) RHHighFFTChirpRows.checked57
    simpa only [RHHighFFTChirpR.rows,RHHighFFTChirpI.rows,RHHighFFTChirpS.rows,
      List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,Nat.reduceMul] using h
  · have h:=RHHighSequentialChirp.sound RHHighFFTChirpR.row58 RHHighFFTChirpI.row58 RHHighFFTChirpS.row58 29696 j
      (by rw [RHHighFFTChirpRows.length58];norm_num at hj;exact hj) RHHighFFTChirpRows.checked58
    simpa only [RHHighFFTChirpR.rows,RHHighFFTChirpI.rows,RHHighFFTChirpS.rows,
      List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,Nat.reduceMul] using h
  · have h:=RHHighSequentialChirp.sound RHHighFFTChirpR.row59 RHHighFFTChirpI.row59 RHHighFFTChirpS.row59 30208 j
      (by rw [RHHighFFTChirpRows.length59];norm_num at hj;exact hj) RHHighFFTChirpRows.checked59
    simpa only [RHHighFFTChirpR.rows,RHHighFFTChirpI.rows,RHHighFFTChirpS.rows,
      List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,Nat.reduceMul] using h
  · have h:=RHHighSequentialChirp.sound RHHighFFTChirpR.row60 RHHighFFTChirpI.row60 RHHighFFTChirpS.row60 30720 j
      (by rw [RHHighFFTChirpRows.length60];norm_num at hj;exact hj) RHHighFFTChirpRows.checked60
    simpa only [RHHighFFTChirpR.rows,RHHighFFTChirpI.rows,RHHighFFTChirpS.rows,
      List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,Nat.reduceMul] using h
  · have h:=RHHighSequentialChirp.sound RHHighFFTChirpR.row61 RHHighFFTChirpI.row61 RHHighFFTChirpS.row61 31232 j
      (by rw [RHHighFFTChirpRows.length61];norm_num at hj;exact hj) RHHighFFTChirpRows.checked61
    simpa only [RHHighFFTChirpR.rows,RHHighFFTChirpI.rows,RHHighFFTChirpS.rows,
      List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,Nat.reduceMul] using h
  · have h:=RHHighSequentialChirp.sound RHHighFFTChirpR.row62 RHHighFFTChirpI.row62 RHHighFFTChirpS.row62 31744 j
      (by rw [RHHighFFTChirpRows.length62];norm_num at hj;exact hj) RHHighFFTChirpRows.checked62
    simpa only [RHHighFFTChirpR.rows,RHHighFFTChirpI.rows,RHHighFFTChirpS.rows,
      List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,Nat.reduceMul] using h
  · have h:=RHHighSequentialChirp.sound RHHighFFTChirpR.row63 RHHighFFTChirpI.row63 RHHighFFTChirpS.row63 32256 j
      (by rw [RHHighFFTChirpRows.length63];norm_num at hj;exact hj) RHHighFFTChirpRows.checked63
    simpa only [RHHighFFTChirpR.rows,RHHighFFTChirpI.rows,RHHighFFTChirpS.rows,
      List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,Nat.reduceMul] using h
