-- Prove2me | solution 1 for TaoFivePrimes.rh_high_height_fft_actual_input00
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T07:03:49.820915+00:00
-- url     : https://prove2.me/submissions/8bb926e3-432b-4588-a331-06c0f411acb3

import Definitions.Def_TaoFivePrimes_RHHighFFTArithmeticBase
import Definitions.Def_TaoFivePrimes_RHHighFFTInputI00
import Definitions.Def_TaoFivePrimes_RHHighFFTInputR00
import Definitions.Def_TaoFivePrimes_RHHighMomentValues00
import Definitions.Def_TaoFivePrimes_RHHighMomentValues01
import Definitions.Def_TaoFivePrimes_RHHighMomentValues02
import Definitions.Def_TaoFivePrimes_RHHighMomentValues03
import Definitions.Def_TaoFivePrimes_RHHighMomentValues04
import Definitions.Def_TaoFivePrimes_RHHighMomentValues05
import Definitions.Def_TaoFivePrimes_RHHighMomentValues06
import Definitions.Def_TaoFivePrimes_RHHighMomentValues07
import Definitions.Def_TaoFivePrimes_RHHighMomentValues08
import Definitions.Def_TaoFivePrimes_RHHighMomentValues09
import Definitions.Def_TaoFivePrimes_RHHighMomentValues10
import Definitions.Def_TaoFivePrimes_RHHighMomentValues11
import Definitions.Def_TaoFivePrimes_RHHighMomentValues12
import Definitions.Def_TaoFivePrimes_RHHighMomentValues13
import Definitions.Def_TaoFivePrimes_RHHighMomentValues14
import Definitions.Def_TaoFivePrimes_RHHighMomentValues15
import Definitions.Def_TaoFivePrimes_RHHighMomentValues16
import Definitions.Def_TaoFivePrimes_RHHighMomentValues17
import Definitions.Def_TaoFivePrimes_RHHighMomentValues18
import Definitions.Def_TaoFivePrimes_RHHighMomentValues19
import Definitions.Def_TaoFivePrimes_RHHighMomentValues20
import Definitions.Def_TaoFivePrimes_RHHighMomentValues21
import Definitions.Def_TaoFivePrimes_RHHighMomentValues22
import Definitions.Def_TaoFivePrimes_RHHighMomentValues23
import Definitions.Def_TaoFivePrimes_RHHighMomentValues24
import Definitions.Def_TaoFivePrimes_RHHighMomentValues25
import Definitions.Def_TaoFivePrimes_RHHighMomentValues26
import Definitions.Def_TaoFivePrimes_RHHighMomentValues27
import Definitions.Def_TaoFivePrimes_RHHighMomentValues28
import Definitions.Def_TaoFivePrimes_RHHighMomentValues29
import Definitions.Def_TaoFivePrimes_RHHighMomentValues30
import Definitions.Def_TaoFivePrimes_RHHighMomentValues31
import Definitions.Def_TaoFivePrimes_RHHighNormalizedMomentArithmetic
import Mathlib
import Theorems.Thm_TaoFivePrimes_rh_high_height_fft_input00_block00
import Theorems.Thm_TaoFivePrimes_rh_high_height_fft_input00_block01
import Theorems.Thm_TaoFivePrimes_rh_high_height_fft_input00_block02
import Theorems.Thm_TaoFivePrimes_rh_high_height_fft_input00_block03
import Theorems.Thm_TaoFivePrimes_rh_high_height_fft_input00_block04
import Theorems.Thm_TaoFivePrimes_rh_high_height_fft_input00_block05
import Theorems.Thm_TaoFivePrimes_rh_high_height_fft_input00_block06
import Theorems.Thm_TaoFivePrimes_rh_high_height_fft_input00_block07
import Theorems.Thm_TaoFivePrimes_rh_high_height_moment_arithmetic_block00
import Theorems.Thm_TaoFivePrimes_rh_high_height_moment_arithmetic_block01
import Theorems.Thm_TaoFivePrimes_rh_high_height_moment_arithmetic_block02
import Theorems.Thm_TaoFivePrimes_rh_high_height_moment_arithmetic_block03
import Theorems.Thm_TaoFivePrimes_rh_high_height_moment_arithmetic_block04
import Theorems.Thm_TaoFivePrimes_rh_high_height_moment_arithmetic_block05
import Theorems.Thm_TaoFivePrimes_rh_high_height_moment_arithmetic_block06
import Theorems.Thm_TaoFivePrimes_rh_high_height_moment_arithmetic_block07
import Theorems.Thm_TaoFivePrimes_rh_high_height_moment_arithmetic_block08
import Theorems.Thm_TaoFivePrimes_rh_high_height_moment_arithmetic_block09
import Theorems.Thm_TaoFivePrimes_rh_high_height_moment_arithmetic_block10
import Theorems.Thm_TaoFivePrimes_rh_high_height_moment_arithmetic_block11
import Theorems.Thm_TaoFivePrimes_rh_high_height_moment_arithmetic_block12
import Theorems.Thm_TaoFivePrimes_rh_high_height_moment_arithmetic_block13
import Theorems.Thm_TaoFivePrimes_rh_high_height_moment_arithmetic_block14
import Theorems.Thm_TaoFivePrimes_rh_high_height_moment_arithmetic_block15
import Theorems.Thm_TaoFivePrimes_rh_high_height_moment_arithmetic_block16
import Theorems.Thm_TaoFivePrimes_rh_high_height_moment_arithmetic_block17
import Theorems.Thm_TaoFivePrimes_rh_high_height_moment_arithmetic_block18
import Theorems.Thm_TaoFivePrimes_rh_high_height_moment_arithmetic_block19
import Theorems.Thm_TaoFivePrimes_rh_high_height_moment_arithmetic_block20
import Theorems.Thm_TaoFivePrimes_rh_high_height_moment_arithmetic_block21
import Theorems.Thm_TaoFivePrimes_rh_high_height_moment_arithmetic_block22
import Theorems.Thm_TaoFivePrimes_rh_high_height_moment_arithmetic_block23
import Theorems.Thm_TaoFivePrimes_rh_high_height_moment_arithmetic_block24
import Theorems.Thm_TaoFivePrimes_rh_high_height_moment_arithmetic_block25
import Theorems.Thm_TaoFivePrimes_rh_high_height_moment_arithmetic_block26
import Theorems.Thm_TaoFivePrimes_rh_high_height_moment_arithmetic_block27
import Theorems.Thm_TaoFivePrimes_rh_high_height_moment_arithmetic_block28
import Theorems.Thm_TaoFivePrimes_rh_high_height_moment_arithmetic_block29
import Theorems.Thm_TaoFivePrimes_rh_high_height_moment_arithmetic_block30
import Theorems.Thm_TaoFivePrimes_rh_high_height_moment_arithmetic_block31
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 1000000
namespace RHHighActualInputReuse00
noncomputable def blocks : List (List (List Nat)) := [RHHighMomentValues00.rows,RHHighMomentValues01.rows,RHHighMomentValues02.rows,RHHighMomentValues03.rows,RHHighMomentValues04.rows,RHHighMomentValues05.rows,RHHighMomentValues06.rows,RHHighMomentValues07.rows,RHHighMomentValues08.rows,RHHighMomentValues09.rows,RHHighMomentValues10.rows,RHHighMomentValues11.rows,RHHighMomentValues12.rows,RHHighMomentValues13.rows,RHHighMomentValues14.rows,RHHighMomentValues15.rows,RHHighMomentValues16.rows,RHHighMomentValues17.rows,RHHighMomentValues18.rows,RHHighMomentValues19.rows,RHHighMomentValues20.rows,RHHighMomentValues21.rows,RHHighMomentValues22.rows,RHHighMomentValues23.rows,RHHighMomentValues24.rows,RHHighMomentValues25.rows,RHHighMomentValues26.rows,RHHighMomentValues27.rows,RHHighMomentValues28.rows,RHHighMomentValues29.rows,RHHighMomentValues30.rows,RHHighMomentValues31.rows]
noncomputable def wordRow (b c : Nat) : List Nat := (((blocks[b]?).getD [])[c]?).getD []
lemma moment_words (b c j q : Nat) (hb:b<32) (hc:c<32) (hj:j<16) (hq:q<26) :
    RHHighFFTArithmeticBase.decode (((wordRow b c)[j]?).getD 0) q=
      RHHighMomentArithmetic.moment (512*b+16*c+j) (RHHighGammaArithmetic.compute (512*b+16*c+j)) q := by
  interval_cases b
  · have h:=(TaoFivePrimes.rh_high_height_moment_arithmetic_block00 c hc j hj q hq).symm
    simpa only [wordRow,blocks,RHHighFFTArithmeticBase.decode,RHHighFFTArithmeticBase.fieldBase,
      RHHighFFTArithmeticBase.bias,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,Nat.mul_comm] using h
  · have h:=(TaoFivePrimes.rh_high_height_moment_arithmetic_block01 c hc j hj q hq).symm
    simpa only [wordRow,blocks,RHHighFFTArithmeticBase.decode,RHHighFFTArithmeticBase.fieldBase,
      RHHighFFTArithmeticBase.bias,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,Nat.mul_comm] using h
  · have h:=(TaoFivePrimes.rh_high_height_moment_arithmetic_block02 c hc j hj q hq).symm
    simpa only [wordRow,blocks,RHHighFFTArithmeticBase.decode,RHHighFFTArithmeticBase.fieldBase,
      RHHighFFTArithmeticBase.bias,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,Nat.mul_comm] using h
  · have h:=(TaoFivePrimes.rh_high_height_moment_arithmetic_block03 c hc j hj q hq).symm
    simpa only [wordRow,blocks,RHHighFFTArithmeticBase.decode,RHHighFFTArithmeticBase.fieldBase,
      RHHighFFTArithmeticBase.bias,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,Nat.mul_comm] using h
  · have h:=(TaoFivePrimes.rh_high_height_moment_arithmetic_block04 c hc j hj q hq).symm
    simpa only [wordRow,blocks,RHHighFFTArithmeticBase.decode,RHHighFFTArithmeticBase.fieldBase,
      RHHighFFTArithmeticBase.bias,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,Nat.mul_comm] using h
  · have h:=(TaoFivePrimes.rh_high_height_moment_arithmetic_block05 c hc j hj q hq).symm
    simpa only [wordRow,blocks,RHHighFFTArithmeticBase.decode,RHHighFFTArithmeticBase.fieldBase,
      RHHighFFTArithmeticBase.bias,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,Nat.mul_comm] using h
  · have h:=(TaoFivePrimes.rh_high_height_moment_arithmetic_block06 c hc j hj q hq).symm
    simpa only [wordRow,blocks,RHHighFFTArithmeticBase.decode,RHHighFFTArithmeticBase.fieldBase,
      RHHighFFTArithmeticBase.bias,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,Nat.mul_comm] using h
  · have h:=(TaoFivePrimes.rh_high_height_moment_arithmetic_block07 c hc j hj q hq).symm
    simpa only [wordRow,blocks,RHHighFFTArithmeticBase.decode,RHHighFFTArithmeticBase.fieldBase,
      RHHighFFTArithmeticBase.bias,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,Nat.mul_comm] using h
  · have h:=(TaoFivePrimes.rh_high_height_moment_arithmetic_block08 c hc j hj q hq).symm
    simpa only [wordRow,blocks,RHHighFFTArithmeticBase.decode,RHHighFFTArithmeticBase.fieldBase,
      RHHighFFTArithmeticBase.bias,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,Nat.mul_comm] using h
  · have h:=(TaoFivePrimes.rh_high_height_moment_arithmetic_block09 c hc j hj q hq).symm
    simpa only [wordRow,blocks,RHHighFFTArithmeticBase.decode,RHHighFFTArithmeticBase.fieldBase,
      RHHighFFTArithmeticBase.bias,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,Nat.mul_comm] using h
  · have h:=(TaoFivePrimes.rh_high_height_moment_arithmetic_block10 c hc j hj q hq).symm
    simpa only [wordRow,blocks,RHHighFFTArithmeticBase.decode,RHHighFFTArithmeticBase.fieldBase,
      RHHighFFTArithmeticBase.bias,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,Nat.mul_comm] using h
  · have h:=(TaoFivePrimes.rh_high_height_moment_arithmetic_block11 c hc j hj q hq).symm
    simpa only [wordRow,blocks,RHHighFFTArithmeticBase.decode,RHHighFFTArithmeticBase.fieldBase,
      RHHighFFTArithmeticBase.bias,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,Nat.mul_comm] using h
  · have h:=(TaoFivePrimes.rh_high_height_moment_arithmetic_block12 c hc j hj q hq).symm
    simpa only [wordRow,blocks,RHHighFFTArithmeticBase.decode,RHHighFFTArithmeticBase.fieldBase,
      RHHighFFTArithmeticBase.bias,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,Nat.mul_comm] using h
  · have h:=(TaoFivePrimes.rh_high_height_moment_arithmetic_block13 c hc j hj q hq).symm
    simpa only [wordRow,blocks,RHHighFFTArithmeticBase.decode,RHHighFFTArithmeticBase.fieldBase,
      RHHighFFTArithmeticBase.bias,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,Nat.mul_comm] using h
  · have h:=(TaoFivePrimes.rh_high_height_moment_arithmetic_block14 c hc j hj q hq).symm
    simpa only [wordRow,blocks,RHHighFFTArithmeticBase.decode,RHHighFFTArithmeticBase.fieldBase,
      RHHighFFTArithmeticBase.bias,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,Nat.mul_comm] using h
  · have h:=(TaoFivePrimes.rh_high_height_moment_arithmetic_block15 c hc j hj q hq).symm
    simpa only [wordRow,blocks,RHHighFFTArithmeticBase.decode,RHHighFFTArithmeticBase.fieldBase,
      RHHighFFTArithmeticBase.bias,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,Nat.mul_comm] using h
  · have h:=(TaoFivePrimes.rh_high_height_moment_arithmetic_block16 c hc j hj q hq).symm
    simpa only [wordRow,blocks,RHHighFFTArithmeticBase.decode,RHHighFFTArithmeticBase.fieldBase,
      RHHighFFTArithmeticBase.bias,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,Nat.mul_comm] using h
  · have h:=(TaoFivePrimes.rh_high_height_moment_arithmetic_block17 c hc j hj q hq).symm
    simpa only [wordRow,blocks,RHHighFFTArithmeticBase.decode,RHHighFFTArithmeticBase.fieldBase,
      RHHighFFTArithmeticBase.bias,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,Nat.mul_comm] using h
  · have h:=(TaoFivePrimes.rh_high_height_moment_arithmetic_block18 c hc j hj q hq).symm
    simpa only [wordRow,blocks,RHHighFFTArithmeticBase.decode,RHHighFFTArithmeticBase.fieldBase,
      RHHighFFTArithmeticBase.bias,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,Nat.mul_comm] using h
  · have h:=(TaoFivePrimes.rh_high_height_moment_arithmetic_block19 c hc j hj q hq).symm
    simpa only [wordRow,blocks,RHHighFFTArithmeticBase.decode,RHHighFFTArithmeticBase.fieldBase,
      RHHighFFTArithmeticBase.bias,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,Nat.mul_comm] using h
  · have h:=(TaoFivePrimes.rh_high_height_moment_arithmetic_block20 c hc j hj q hq).symm
    simpa only [wordRow,blocks,RHHighFFTArithmeticBase.decode,RHHighFFTArithmeticBase.fieldBase,
      RHHighFFTArithmeticBase.bias,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,Nat.mul_comm] using h
  · have h:=(TaoFivePrimes.rh_high_height_moment_arithmetic_block21 c hc j hj q hq).symm
    simpa only [wordRow,blocks,RHHighFFTArithmeticBase.decode,RHHighFFTArithmeticBase.fieldBase,
      RHHighFFTArithmeticBase.bias,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,Nat.mul_comm] using h
  · have h:=(TaoFivePrimes.rh_high_height_moment_arithmetic_block22 c hc j hj q hq).symm
    simpa only [wordRow,blocks,RHHighFFTArithmeticBase.decode,RHHighFFTArithmeticBase.fieldBase,
      RHHighFFTArithmeticBase.bias,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,Nat.mul_comm] using h
  · have h:=(TaoFivePrimes.rh_high_height_moment_arithmetic_block23 c hc j hj q hq).symm
    simpa only [wordRow,blocks,RHHighFFTArithmeticBase.decode,RHHighFFTArithmeticBase.fieldBase,
      RHHighFFTArithmeticBase.bias,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,Nat.mul_comm] using h
  · have h:=(TaoFivePrimes.rh_high_height_moment_arithmetic_block24 c hc j hj q hq).symm
    simpa only [wordRow,blocks,RHHighFFTArithmeticBase.decode,RHHighFFTArithmeticBase.fieldBase,
      RHHighFFTArithmeticBase.bias,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,Nat.mul_comm] using h
  · have h:=(TaoFivePrimes.rh_high_height_moment_arithmetic_block25 c hc j hj q hq).symm
    simpa only [wordRow,blocks,RHHighFFTArithmeticBase.decode,RHHighFFTArithmeticBase.fieldBase,
      RHHighFFTArithmeticBase.bias,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,Nat.mul_comm] using h
  · have h:=(TaoFivePrimes.rh_high_height_moment_arithmetic_block26 c hc j hj q hq).symm
    simpa only [wordRow,blocks,RHHighFFTArithmeticBase.decode,RHHighFFTArithmeticBase.fieldBase,
      RHHighFFTArithmeticBase.bias,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,Nat.mul_comm] using h
  · have h:=(TaoFivePrimes.rh_high_height_moment_arithmetic_block27 c hc j hj q hq).symm
    simpa only [wordRow,blocks,RHHighFFTArithmeticBase.decode,RHHighFFTArithmeticBase.fieldBase,
      RHHighFFTArithmeticBase.bias,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,Nat.mul_comm] using h
  · have h:=(TaoFivePrimes.rh_high_height_moment_arithmetic_block28 c hc j hj q hq).symm
    simpa only [wordRow,blocks,RHHighFFTArithmeticBase.decode,RHHighFFTArithmeticBase.fieldBase,
      RHHighFFTArithmeticBase.bias,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,Nat.mul_comm] using h
  · have h:=(TaoFivePrimes.rh_high_height_moment_arithmetic_block29 c hc j hj q hq).symm
    simpa only [wordRow,blocks,RHHighFFTArithmeticBase.decode,RHHighFFTArithmeticBase.fieldBase,
      RHHighFFTArithmeticBase.bias,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,Nat.mul_comm] using h
  · have h:=(TaoFivePrimes.rh_high_height_moment_arithmetic_block30 c hc j hj q hq).symm
    simpa only [wordRow,blocks,RHHighFFTArithmeticBase.decode,RHHighFFTArithmeticBase.fieldBase,
      RHHighFFTArithmeticBase.bias,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,Nat.mul_comm] using h
  · have h:=(TaoFivePrimes.rh_high_height_moment_arithmetic_block31 c hc j hj q hq).symm
    simpa only [wordRow,blocks,RHHighFFTArithmeticBase.decode,RHHighFFTArithmeticBase.fieldBase,
      RHHighFFTArithmeticBase.bias,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,Nat.mul_comm] using h
lemma raw_words (b c j : Nat) (hb:b<32) (hc:c<32) (hj:j<16) :
    RHHighFFTArithmeticBase.raw (((wordRow b c)[j]?).getD 0) 0 (512*b+16*c+j)=
      (((((RHHighFFTInputR00.rows[b]?).getD [])[16*c+j]?).getD 0:Int)-2^166,
       ((((RHHighFFTInputI00.rows[b]?).getD [])[16*c+j]?).getD 0:Int)-2^166) := by
  have h6:(16*c+j)/16=c:=by omega
  interval_cases b
  · have h:=TaoFivePrimes.rh_high_height_fft_input00_block00 (512*0+16*c+j) (by omega)
    have h0:(512*0+16*c+j)/512=0:=by omega
    have h1:((512*0+16*c+j)%512)/16=c:=by omega
    have h2:(512*0+16*c+j)%16=j:=by omega
    have h3:0+(512*0+16*c+j)=(512*0+16*c+j):=by omega
    have h4:(512*0+16*c+j)/512=0:=by omega
    have h5:(512*0+16*c+j)%512=16*c+j:=by omega
    dsimp only [RHHighFFTMomentBlock00.word] at h
    simp only [h0,h1,h2,h3,h4,h5,h6] at h
    simpa only [wordRow,blocks,RHHighFFTMomentBlock00.blocks,List.getElem?_cons_zero,
      List.getElem?_cons_succ,Option.getD_some] using h
  · have h:=TaoFivePrimes.rh_high_height_fft_input00_block00 (512*1+16*c+j) (by omega)
    have h0:(512*1+16*c+j)/512=1:=by omega
    have h1:((512*1+16*c+j)%512)/16=c:=by omega
    have h2:(512*1+16*c+j)%16=j:=by omega
    have h3:0+(512*1+16*c+j)=(512*1+16*c+j):=by omega
    have h4:(512*1+16*c+j)/512=1:=by omega
    have h5:(512*1+16*c+j)%512=16*c+j:=by omega
    dsimp only [RHHighFFTMomentBlock00.word] at h
    simp only [h0,h1,h2,h3,h4,h5,h6] at h
    simpa only [wordRow,blocks,RHHighFFTMomentBlock00.blocks,List.getElem?_cons_zero,
      List.getElem?_cons_succ,Option.getD_some] using h
  · have h:=TaoFivePrimes.rh_high_height_fft_input00_block00 (512*2+16*c+j) (by omega)
    have h0:(512*2+16*c+j)/512=2:=by omega
    have h1:((512*2+16*c+j)%512)/16=c:=by omega
    have h2:(512*2+16*c+j)%16=j:=by omega
    have h3:0+(512*2+16*c+j)=(512*2+16*c+j):=by omega
    have h4:(512*2+16*c+j)/512=2:=by omega
    have h5:(512*2+16*c+j)%512=16*c+j:=by omega
    dsimp only [RHHighFFTMomentBlock00.word] at h
    simp only [h0,h1,h2,h3,h4,h5,h6] at h
    simpa only [wordRow,blocks,RHHighFFTMomentBlock00.blocks,List.getElem?_cons_zero,
      List.getElem?_cons_succ,Option.getD_some] using h
  · have h:=TaoFivePrimes.rh_high_height_fft_input00_block00 (512*3+16*c+j) (by omega)
    have h0:(512*3+16*c+j)/512=3:=by omega
    have h1:((512*3+16*c+j)%512)/16=c:=by omega
    have h2:(512*3+16*c+j)%16=j:=by omega
    have h3:0+(512*3+16*c+j)=(512*3+16*c+j):=by omega
    have h4:(512*3+16*c+j)/512=3:=by omega
    have h5:(512*3+16*c+j)%512=16*c+j:=by omega
    dsimp only [RHHighFFTMomentBlock00.word] at h
    simp only [h0,h1,h2,h3,h4,h5,h6] at h
    simpa only [wordRow,blocks,RHHighFFTMomentBlock00.blocks,List.getElem?_cons_zero,
      List.getElem?_cons_succ,Option.getD_some] using h
  · have h:=TaoFivePrimes.rh_high_height_fft_input00_block01 (512*0+16*c+j) (by omega)
    have h0:(512*0+16*c+j)/512=0:=by omega
    have h1:((512*0+16*c+j)%512)/16=c:=by omega
    have h2:(512*0+16*c+j)%16=j:=by omega
    have h3:2048+(512*0+16*c+j)=(512*4+16*c+j):=by omega
    have h4:(512*4+16*c+j)/512=4:=by omega
    have h5:(512*4+16*c+j)%512=16*c+j:=by omega
    dsimp only [RHHighFFTMomentBlock01.word] at h
    simp only [h0,h1,h2,h3,h4,h5,h6] at h
    simpa only [wordRow,blocks,RHHighFFTMomentBlock01.blocks,List.getElem?_cons_zero,
      List.getElem?_cons_succ,Option.getD_some] using h
  · have h:=TaoFivePrimes.rh_high_height_fft_input00_block01 (512*1+16*c+j) (by omega)
    have h0:(512*1+16*c+j)/512=1:=by omega
    have h1:((512*1+16*c+j)%512)/16=c:=by omega
    have h2:(512*1+16*c+j)%16=j:=by omega
    have h3:2048+(512*1+16*c+j)=(512*5+16*c+j):=by omega
    have h4:(512*5+16*c+j)/512=5:=by omega
    have h5:(512*5+16*c+j)%512=16*c+j:=by omega
    dsimp only [RHHighFFTMomentBlock01.word] at h
    simp only [h0,h1,h2,h3,h4,h5,h6] at h
    simpa only [wordRow,blocks,RHHighFFTMomentBlock01.blocks,List.getElem?_cons_zero,
      List.getElem?_cons_succ,Option.getD_some] using h
  · have h:=TaoFivePrimes.rh_high_height_fft_input00_block01 (512*2+16*c+j) (by omega)
    have h0:(512*2+16*c+j)/512=2:=by omega
    have h1:((512*2+16*c+j)%512)/16=c:=by omega
    have h2:(512*2+16*c+j)%16=j:=by omega
    have h3:2048+(512*2+16*c+j)=(512*6+16*c+j):=by omega
    have h4:(512*6+16*c+j)/512=6:=by omega
    have h5:(512*6+16*c+j)%512=16*c+j:=by omega
    dsimp only [RHHighFFTMomentBlock01.word] at h
    simp only [h0,h1,h2,h3,h4,h5,h6] at h
    simpa only [wordRow,blocks,RHHighFFTMomentBlock01.blocks,List.getElem?_cons_zero,
      List.getElem?_cons_succ,Option.getD_some] using h
  · have h:=TaoFivePrimes.rh_high_height_fft_input00_block01 (512*3+16*c+j) (by omega)
    have h0:(512*3+16*c+j)/512=3:=by omega
    have h1:((512*3+16*c+j)%512)/16=c:=by omega
    have h2:(512*3+16*c+j)%16=j:=by omega
    have h3:2048+(512*3+16*c+j)=(512*7+16*c+j):=by omega
    have h4:(512*7+16*c+j)/512=7:=by omega
    have h5:(512*7+16*c+j)%512=16*c+j:=by omega
    dsimp only [RHHighFFTMomentBlock01.word] at h
    simp only [h0,h1,h2,h3,h4,h5,h6] at h
    simpa only [wordRow,blocks,RHHighFFTMomentBlock01.blocks,List.getElem?_cons_zero,
      List.getElem?_cons_succ,Option.getD_some] using h
  · have h:=TaoFivePrimes.rh_high_height_fft_input00_block02 (512*0+16*c+j) (by omega)
    have h0:(512*0+16*c+j)/512=0:=by omega
    have h1:((512*0+16*c+j)%512)/16=c:=by omega
    have h2:(512*0+16*c+j)%16=j:=by omega
    have h3:4096+(512*0+16*c+j)=(512*8+16*c+j):=by omega
    have h4:(512*8+16*c+j)/512=8:=by omega
    have h5:(512*8+16*c+j)%512=16*c+j:=by omega
    dsimp only [RHHighFFTMomentBlock02.word] at h
    simp only [h0,h1,h2,h3,h4,h5,h6] at h
    simpa only [wordRow,blocks,RHHighFFTMomentBlock02.blocks,List.getElem?_cons_zero,
      List.getElem?_cons_succ,Option.getD_some] using h
  · have h:=TaoFivePrimes.rh_high_height_fft_input00_block02 (512*1+16*c+j) (by omega)
    have h0:(512*1+16*c+j)/512=1:=by omega
    have h1:((512*1+16*c+j)%512)/16=c:=by omega
    have h2:(512*1+16*c+j)%16=j:=by omega
    have h3:4096+(512*1+16*c+j)=(512*9+16*c+j):=by omega
    have h4:(512*9+16*c+j)/512=9:=by omega
    have h5:(512*9+16*c+j)%512=16*c+j:=by omega
    dsimp only [RHHighFFTMomentBlock02.word] at h
    simp only [h0,h1,h2,h3,h4,h5,h6] at h
    simpa only [wordRow,blocks,RHHighFFTMomentBlock02.blocks,List.getElem?_cons_zero,
      List.getElem?_cons_succ,Option.getD_some] using h
  · have h:=TaoFivePrimes.rh_high_height_fft_input00_block02 (512*2+16*c+j) (by omega)
    have h0:(512*2+16*c+j)/512=2:=by omega
    have h1:((512*2+16*c+j)%512)/16=c:=by omega
    have h2:(512*2+16*c+j)%16=j:=by omega
    have h3:4096+(512*2+16*c+j)=(512*10+16*c+j):=by omega
    have h4:(512*10+16*c+j)/512=10:=by omega
    have h5:(512*10+16*c+j)%512=16*c+j:=by omega
    dsimp only [RHHighFFTMomentBlock02.word] at h
    simp only [h0,h1,h2,h3,h4,h5,h6] at h
    simpa only [wordRow,blocks,RHHighFFTMomentBlock02.blocks,List.getElem?_cons_zero,
      List.getElem?_cons_succ,Option.getD_some] using h
  · have h:=TaoFivePrimes.rh_high_height_fft_input00_block02 (512*3+16*c+j) (by omega)
    have h0:(512*3+16*c+j)/512=3:=by omega
    have h1:((512*3+16*c+j)%512)/16=c:=by omega
    have h2:(512*3+16*c+j)%16=j:=by omega
    have h3:4096+(512*3+16*c+j)=(512*11+16*c+j):=by omega
    have h4:(512*11+16*c+j)/512=11:=by omega
    have h5:(512*11+16*c+j)%512=16*c+j:=by omega
    dsimp only [RHHighFFTMomentBlock02.word] at h
    simp only [h0,h1,h2,h3,h4,h5,h6] at h
    simpa only [wordRow,blocks,RHHighFFTMomentBlock02.blocks,List.getElem?_cons_zero,
      List.getElem?_cons_succ,Option.getD_some] using h
  · have h:=TaoFivePrimes.rh_high_height_fft_input00_block03 (512*0+16*c+j) (by omega)
    have h0:(512*0+16*c+j)/512=0:=by omega
    have h1:((512*0+16*c+j)%512)/16=c:=by omega
    have h2:(512*0+16*c+j)%16=j:=by omega
    have h3:6144+(512*0+16*c+j)=(512*12+16*c+j):=by omega
    have h4:(512*12+16*c+j)/512=12:=by omega
    have h5:(512*12+16*c+j)%512=16*c+j:=by omega
    dsimp only [RHHighFFTMomentBlock03.word] at h
    simp only [h0,h1,h2,h3,h4,h5,h6] at h
    simpa only [wordRow,blocks,RHHighFFTMomentBlock03.blocks,List.getElem?_cons_zero,
      List.getElem?_cons_succ,Option.getD_some] using h
  · have h:=TaoFivePrimes.rh_high_height_fft_input00_block03 (512*1+16*c+j) (by omega)
    have h0:(512*1+16*c+j)/512=1:=by omega
    have h1:((512*1+16*c+j)%512)/16=c:=by omega
    have h2:(512*1+16*c+j)%16=j:=by omega
    have h3:6144+(512*1+16*c+j)=(512*13+16*c+j):=by omega
    have h4:(512*13+16*c+j)/512=13:=by omega
    have h5:(512*13+16*c+j)%512=16*c+j:=by omega
    dsimp only [RHHighFFTMomentBlock03.word] at h
    simp only [h0,h1,h2,h3,h4,h5,h6] at h
    simpa only [wordRow,blocks,RHHighFFTMomentBlock03.blocks,List.getElem?_cons_zero,
      List.getElem?_cons_succ,Option.getD_some] using h
  · have h:=TaoFivePrimes.rh_high_height_fft_input00_block03 (512*2+16*c+j) (by omega)
    have h0:(512*2+16*c+j)/512=2:=by omega
    have h1:((512*2+16*c+j)%512)/16=c:=by omega
    have h2:(512*2+16*c+j)%16=j:=by omega
    have h3:6144+(512*2+16*c+j)=(512*14+16*c+j):=by omega
    have h4:(512*14+16*c+j)/512=14:=by omega
    have h5:(512*14+16*c+j)%512=16*c+j:=by omega
    dsimp only [RHHighFFTMomentBlock03.word] at h
    simp only [h0,h1,h2,h3,h4,h5,h6] at h
    simpa only [wordRow,blocks,RHHighFFTMomentBlock03.blocks,List.getElem?_cons_zero,
      List.getElem?_cons_succ,Option.getD_some] using h
  · have h:=TaoFivePrimes.rh_high_height_fft_input00_block03 (512*3+16*c+j) (by omega)
    have h0:(512*3+16*c+j)/512=3:=by omega
    have h1:((512*3+16*c+j)%512)/16=c:=by omega
    have h2:(512*3+16*c+j)%16=j:=by omega
    have h3:6144+(512*3+16*c+j)=(512*15+16*c+j):=by omega
    have h4:(512*15+16*c+j)/512=15:=by omega
    have h5:(512*15+16*c+j)%512=16*c+j:=by omega
    dsimp only [RHHighFFTMomentBlock03.word] at h
    simp only [h0,h1,h2,h3,h4,h5,h6] at h
    simpa only [wordRow,blocks,RHHighFFTMomentBlock03.blocks,List.getElem?_cons_zero,
      List.getElem?_cons_succ,Option.getD_some] using h
  · have h:=TaoFivePrimes.rh_high_height_fft_input00_block04 (512*0+16*c+j) (by omega)
    have h0:(512*0+16*c+j)/512=0:=by omega
    have h1:((512*0+16*c+j)%512)/16=c:=by omega
    have h2:(512*0+16*c+j)%16=j:=by omega
    have h3:8192+(512*0+16*c+j)=(512*16+16*c+j):=by omega
    have h4:(512*16+16*c+j)/512=16:=by omega
    have h5:(512*16+16*c+j)%512=16*c+j:=by omega
    dsimp only [RHHighFFTMomentBlock04.word] at h
    simp only [h0,h1,h2,h3,h4,h5,h6] at h
    simpa only [wordRow,blocks,RHHighFFTMomentBlock04.blocks,List.getElem?_cons_zero,
      List.getElem?_cons_succ,Option.getD_some] using h
  · have h:=TaoFivePrimes.rh_high_height_fft_input00_block04 (512*1+16*c+j) (by omega)
    have h0:(512*1+16*c+j)/512=1:=by omega
    have h1:((512*1+16*c+j)%512)/16=c:=by omega
    have h2:(512*1+16*c+j)%16=j:=by omega
    have h3:8192+(512*1+16*c+j)=(512*17+16*c+j):=by omega
    have h4:(512*17+16*c+j)/512=17:=by omega
    have h5:(512*17+16*c+j)%512=16*c+j:=by omega
    dsimp only [RHHighFFTMomentBlock04.word] at h
    simp only [h0,h1,h2,h3,h4,h5,h6] at h
    simpa only [wordRow,blocks,RHHighFFTMomentBlock04.blocks,List.getElem?_cons_zero,
      List.getElem?_cons_succ,Option.getD_some] using h
  · have h:=TaoFivePrimes.rh_high_height_fft_input00_block04 (512*2+16*c+j) (by omega)
    have h0:(512*2+16*c+j)/512=2:=by omega
    have h1:((512*2+16*c+j)%512)/16=c:=by omega
    have h2:(512*2+16*c+j)%16=j:=by omega
    have h3:8192+(512*2+16*c+j)=(512*18+16*c+j):=by omega
    have h4:(512*18+16*c+j)/512=18:=by omega
    have h5:(512*18+16*c+j)%512=16*c+j:=by omega
    dsimp only [RHHighFFTMomentBlock04.word] at h
    simp only [h0,h1,h2,h3,h4,h5,h6] at h
    simpa only [wordRow,blocks,RHHighFFTMomentBlock04.blocks,List.getElem?_cons_zero,
      List.getElem?_cons_succ,Option.getD_some] using h
  · have h:=TaoFivePrimes.rh_high_height_fft_input00_block04 (512*3+16*c+j) (by omega)
    have h0:(512*3+16*c+j)/512=3:=by omega
    have h1:((512*3+16*c+j)%512)/16=c:=by omega
    have h2:(512*3+16*c+j)%16=j:=by omega
    have h3:8192+(512*3+16*c+j)=(512*19+16*c+j):=by omega
    have h4:(512*19+16*c+j)/512=19:=by omega
    have h5:(512*19+16*c+j)%512=16*c+j:=by omega
    dsimp only [RHHighFFTMomentBlock04.word] at h
    simp only [h0,h1,h2,h3,h4,h5,h6] at h
    simpa only [wordRow,blocks,RHHighFFTMomentBlock04.blocks,List.getElem?_cons_zero,
      List.getElem?_cons_succ,Option.getD_some] using h
  · have h:=TaoFivePrimes.rh_high_height_fft_input00_block05 (512*0+16*c+j) (by omega)
    have h0:(512*0+16*c+j)/512=0:=by omega
    have h1:((512*0+16*c+j)%512)/16=c:=by omega
    have h2:(512*0+16*c+j)%16=j:=by omega
    have h3:10240+(512*0+16*c+j)=(512*20+16*c+j):=by omega
    have h4:(512*20+16*c+j)/512=20:=by omega
    have h5:(512*20+16*c+j)%512=16*c+j:=by omega
    dsimp only [RHHighFFTMomentBlock05.word] at h
    simp only [h0,h1,h2,h3,h4,h5,h6] at h
    simpa only [wordRow,blocks,RHHighFFTMomentBlock05.blocks,List.getElem?_cons_zero,
      List.getElem?_cons_succ,Option.getD_some] using h
  · have h:=TaoFivePrimes.rh_high_height_fft_input00_block05 (512*1+16*c+j) (by omega)
    have h0:(512*1+16*c+j)/512=1:=by omega
    have h1:((512*1+16*c+j)%512)/16=c:=by omega
    have h2:(512*1+16*c+j)%16=j:=by omega
    have h3:10240+(512*1+16*c+j)=(512*21+16*c+j):=by omega
    have h4:(512*21+16*c+j)/512=21:=by omega
    have h5:(512*21+16*c+j)%512=16*c+j:=by omega
    dsimp only [RHHighFFTMomentBlock05.word] at h
    simp only [h0,h1,h2,h3,h4,h5,h6] at h
    simpa only [wordRow,blocks,RHHighFFTMomentBlock05.blocks,List.getElem?_cons_zero,
      List.getElem?_cons_succ,Option.getD_some] using h
  · have h:=TaoFivePrimes.rh_high_height_fft_input00_block05 (512*2+16*c+j) (by omega)
    have h0:(512*2+16*c+j)/512=2:=by omega
    have h1:((512*2+16*c+j)%512)/16=c:=by omega
    have h2:(512*2+16*c+j)%16=j:=by omega
    have h3:10240+(512*2+16*c+j)=(512*22+16*c+j):=by omega
    have h4:(512*22+16*c+j)/512=22:=by omega
    have h5:(512*22+16*c+j)%512=16*c+j:=by omega
    dsimp only [RHHighFFTMomentBlock05.word] at h
    simp only [h0,h1,h2,h3,h4,h5,h6] at h
    simpa only [wordRow,blocks,RHHighFFTMomentBlock05.blocks,List.getElem?_cons_zero,
      List.getElem?_cons_succ,Option.getD_some] using h
  · have h:=TaoFivePrimes.rh_high_height_fft_input00_block05 (512*3+16*c+j) (by omega)
    have h0:(512*3+16*c+j)/512=3:=by omega
    have h1:((512*3+16*c+j)%512)/16=c:=by omega
    have h2:(512*3+16*c+j)%16=j:=by omega
    have h3:10240+(512*3+16*c+j)=(512*23+16*c+j):=by omega
    have h4:(512*23+16*c+j)/512=23:=by omega
    have h5:(512*23+16*c+j)%512=16*c+j:=by omega
    dsimp only [RHHighFFTMomentBlock05.word] at h
    simp only [h0,h1,h2,h3,h4,h5,h6] at h
    simpa only [wordRow,blocks,RHHighFFTMomentBlock05.blocks,List.getElem?_cons_zero,
      List.getElem?_cons_succ,Option.getD_some] using h
  · have h:=TaoFivePrimes.rh_high_height_fft_input00_block06 (512*0+16*c+j) (by omega)
    have h0:(512*0+16*c+j)/512=0:=by omega
    have h1:((512*0+16*c+j)%512)/16=c:=by omega
    have h2:(512*0+16*c+j)%16=j:=by omega
    have h3:12288+(512*0+16*c+j)=(512*24+16*c+j):=by omega
    have h4:(512*24+16*c+j)/512=24:=by omega
    have h5:(512*24+16*c+j)%512=16*c+j:=by omega
    dsimp only [RHHighFFTMomentBlock06.word] at h
    simp only [h0,h1,h2,h3,h4,h5,h6] at h
    simpa only [wordRow,blocks,RHHighFFTMomentBlock06.blocks,List.getElem?_cons_zero,
      List.getElem?_cons_succ,Option.getD_some] using h
  · have h:=TaoFivePrimes.rh_high_height_fft_input00_block06 (512*1+16*c+j) (by omega)
    have h0:(512*1+16*c+j)/512=1:=by omega
    have h1:((512*1+16*c+j)%512)/16=c:=by omega
    have h2:(512*1+16*c+j)%16=j:=by omega
    have h3:12288+(512*1+16*c+j)=(512*25+16*c+j):=by omega
    have h4:(512*25+16*c+j)/512=25:=by omega
    have h5:(512*25+16*c+j)%512=16*c+j:=by omega
    dsimp only [RHHighFFTMomentBlock06.word] at h
    simp only [h0,h1,h2,h3,h4,h5,h6] at h
    simpa only [wordRow,blocks,RHHighFFTMomentBlock06.blocks,List.getElem?_cons_zero,
      List.getElem?_cons_succ,Option.getD_some] using h
  · have h:=TaoFivePrimes.rh_high_height_fft_input00_block06 (512*2+16*c+j) (by omega)
    have h0:(512*2+16*c+j)/512=2:=by omega
    have h1:((512*2+16*c+j)%512)/16=c:=by omega
    have h2:(512*2+16*c+j)%16=j:=by omega
    have h3:12288+(512*2+16*c+j)=(512*26+16*c+j):=by omega
    have h4:(512*26+16*c+j)/512=26:=by omega
    have h5:(512*26+16*c+j)%512=16*c+j:=by omega
    dsimp only [RHHighFFTMomentBlock06.word] at h
    simp only [h0,h1,h2,h3,h4,h5,h6] at h
    simpa only [wordRow,blocks,RHHighFFTMomentBlock06.blocks,List.getElem?_cons_zero,
      List.getElem?_cons_succ,Option.getD_some] using h
  · have h:=TaoFivePrimes.rh_high_height_fft_input00_block06 (512*3+16*c+j) (by omega)
    have h0:(512*3+16*c+j)/512=3:=by omega
    have h1:((512*3+16*c+j)%512)/16=c:=by omega
    have h2:(512*3+16*c+j)%16=j:=by omega
    have h3:12288+(512*3+16*c+j)=(512*27+16*c+j):=by omega
    have h4:(512*27+16*c+j)/512=27:=by omega
    have h5:(512*27+16*c+j)%512=16*c+j:=by omega
    dsimp only [RHHighFFTMomentBlock06.word] at h
    simp only [h0,h1,h2,h3,h4,h5,h6] at h
    simpa only [wordRow,blocks,RHHighFFTMomentBlock06.blocks,List.getElem?_cons_zero,
      List.getElem?_cons_succ,Option.getD_some] using h
  · have h:=TaoFivePrimes.rh_high_height_fft_input00_block07 (512*0+16*c+j) (by omega)
    have h0:(512*0+16*c+j)/512=0:=by omega
    have h1:((512*0+16*c+j)%512)/16=c:=by omega
    have h2:(512*0+16*c+j)%16=j:=by omega
    have h3:14336+(512*0+16*c+j)=(512*28+16*c+j):=by omega
    have h4:(512*28+16*c+j)/512=28:=by omega
    have h5:(512*28+16*c+j)%512=16*c+j:=by omega
    dsimp only [RHHighFFTMomentBlock07.word] at h
    simp only [h0,h1,h2,h3,h4,h5,h6] at h
    simpa only [wordRow,blocks,RHHighFFTMomentBlock07.blocks,List.getElem?_cons_zero,
      List.getElem?_cons_succ,Option.getD_some] using h
  · have h:=TaoFivePrimes.rh_high_height_fft_input00_block07 (512*1+16*c+j) (by omega)
    have h0:(512*1+16*c+j)/512=1:=by omega
    have h1:((512*1+16*c+j)%512)/16=c:=by omega
    have h2:(512*1+16*c+j)%16=j:=by omega
    have h3:14336+(512*1+16*c+j)=(512*29+16*c+j):=by omega
    have h4:(512*29+16*c+j)/512=29:=by omega
    have h5:(512*29+16*c+j)%512=16*c+j:=by omega
    dsimp only [RHHighFFTMomentBlock07.word] at h
    simp only [h0,h1,h2,h3,h4,h5,h6] at h
    simpa only [wordRow,blocks,RHHighFFTMomentBlock07.blocks,List.getElem?_cons_zero,
      List.getElem?_cons_succ,Option.getD_some] using h
  · have h:=TaoFivePrimes.rh_high_height_fft_input00_block07 (512*2+16*c+j) (by omega)
    have h0:(512*2+16*c+j)/512=2:=by omega
    have h1:((512*2+16*c+j)%512)/16=c:=by omega
    have h2:(512*2+16*c+j)%16=j:=by omega
    have h3:14336+(512*2+16*c+j)=(512*30+16*c+j):=by omega
    have h4:(512*30+16*c+j)/512=30:=by omega
    have h5:(512*30+16*c+j)%512=16*c+j:=by omega
    dsimp only [RHHighFFTMomentBlock07.word] at h
    simp only [h0,h1,h2,h3,h4,h5,h6] at h
    simpa only [wordRow,blocks,RHHighFFTMomentBlock07.blocks,List.getElem?_cons_zero,
      List.getElem?_cons_succ,Option.getD_some] using h
  · have h:=TaoFivePrimes.rh_high_height_fft_input00_block07 (512*3+16*c+j) (by omega)
    have h0:(512*3+16*c+j)/512=3:=by omega
    have h1:((512*3+16*c+j)%512)/16=c:=by omega
    have h2:(512*3+16*c+j)%16=j:=by omega
    have h3:14336+(512*3+16*c+j)=(512*31+16*c+j):=by omega
    have h4:(512*31+16*c+j)/512=31:=by omega
    have h5:(512*31+16*c+j)%512=16*c+j:=by omega
    dsimp only [RHHighFFTMomentBlock07.word] at h
    simp only [h0,h1,h2,h3,h4,h5,h6] at h
    simpa only [wordRow,blocks,RHHighFFTMomentBlock07.blocks,List.getElem?_cons_zero,
      List.getElem?_cons_succ,Option.getD_some] using h
end RHHighActualInputReuse00
theorem solution :
  ∀ i : Nat,i<16384 →
  let m:=RHHighMomentArithmetic.moment i (RHHighGammaArithmetic.compute i) 0
  let c:=RHHighFFTArithmeticBase.chirp i
  (m.1*c.1+m.2*c.2,m.2*c.1-m.1*c.2)=
    ((((((RHHighFFTInputR00.rows[i/512]?).getD [])[i%512]?).getD 0:Nat):Int)-2^166,
     (((((RHHighFFTInputI00.rows[i/512]?).getD [])[i%512]?).getD 0:Nat):Int)-2^166) := by
  intro i hi
  let b:=i/512
  let c:=(i%512)/16
  let j:=i%16
  have hb:b<32:=by dsimp [b];omega
  have hc:c<32:=by dsimp [c];omega
  have hj:j<16:=by dsimp [j];omega
  have h:=RHHighActualInputReuse00.raw_words b c j hb hc hj
  have hw:=RHHighActualInputReuse00.moment_words b c j 0 hb hc hj (by decide)
  unfold RHHighFFTArithmeticBase.raw at h
  rw [hw] at h
  have hi':512*b+16*c+j=i:=by dsimp [b,c,j];omega
  have hcj:16*c+j=i%512:=by dsimp [c,j];omega
  rw [hi',hcj] at h
  exact h
