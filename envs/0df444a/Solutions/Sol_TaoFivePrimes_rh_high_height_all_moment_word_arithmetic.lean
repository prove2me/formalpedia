-- Prove2me | solution 1 for TaoFivePrimes.rh_high_height_all_moment_word_arithmetic
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T07:31:43.759281+00:00
-- url     : https://prove2.me/submissions/66637cd8-14f0-40c0-903c-8fade28150ec

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighAllMomentWords
import Definitions.Def_TaoFivePrimes_RHHighNormalizedMomentArithmetic
import Definitions.Def_TaoFivePrimes_RHHighFFTArithmeticBase
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
namespace RHHighAllMomentArithmetic
noncomputable def wordRow (b c : Nat) : List Nat := (((RHHighAllMomentWords.blocks[b]?).getD [])[c]?).getD []
lemma moment_words (b c j q : Nat) (hb:b<32) (hc:c<32) (hj:j<16) (hq:q<26) :
    RHHighFFTArithmeticBase.decode (((wordRow b c)[j]?).getD 0) q=
      RHHighMomentArithmetic.moment (512*b+16*c+j) (RHHighGammaArithmetic.compute (512*b+16*c+j)) q := by
  interval_cases b
  · have h:=(TaoFivePrimes.rh_high_height_moment_arithmetic_block00 c hc j hj q hq).symm
    simpa only [wordRow,RHHighAllMomentWords.blocks,RHHighFFTArithmeticBase.decode,RHHighFFTArithmeticBase.fieldBase,
      RHHighFFTArithmeticBase.bias,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,Nat.mul_comm] using h
  · have h:=(TaoFivePrimes.rh_high_height_moment_arithmetic_block01 c hc j hj q hq).symm
    simpa only [wordRow,RHHighAllMomentWords.blocks,RHHighFFTArithmeticBase.decode,RHHighFFTArithmeticBase.fieldBase,
      RHHighFFTArithmeticBase.bias,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,Nat.mul_comm] using h
  · have h:=(TaoFivePrimes.rh_high_height_moment_arithmetic_block02 c hc j hj q hq).symm
    simpa only [wordRow,RHHighAllMomentWords.blocks,RHHighFFTArithmeticBase.decode,RHHighFFTArithmeticBase.fieldBase,
      RHHighFFTArithmeticBase.bias,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,Nat.mul_comm] using h
  · have h:=(TaoFivePrimes.rh_high_height_moment_arithmetic_block03 c hc j hj q hq).symm
    simpa only [wordRow,RHHighAllMomentWords.blocks,RHHighFFTArithmeticBase.decode,RHHighFFTArithmeticBase.fieldBase,
      RHHighFFTArithmeticBase.bias,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,Nat.mul_comm] using h
  · have h:=(TaoFivePrimes.rh_high_height_moment_arithmetic_block04 c hc j hj q hq).symm
    simpa only [wordRow,RHHighAllMomentWords.blocks,RHHighFFTArithmeticBase.decode,RHHighFFTArithmeticBase.fieldBase,
      RHHighFFTArithmeticBase.bias,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,Nat.mul_comm] using h
  · have h:=(TaoFivePrimes.rh_high_height_moment_arithmetic_block05 c hc j hj q hq).symm
    simpa only [wordRow,RHHighAllMomentWords.blocks,RHHighFFTArithmeticBase.decode,RHHighFFTArithmeticBase.fieldBase,
      RHHighFFTArithmeticBase.bias,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,Nat.mul_comm] using h
  · have h:=(TaoFivePrimes.rh_high_height_moment_arithmetic_block06 c hc j hj q hq).symm
    simpa only [wordRow,RHHighAllMomentWords.blocks,RHHighFFTArithmeticBase.decode,RHHighFFTArithmeticBase.fieldBase,
      RHHighFFTArithmeticBase.bias,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,Nat.mul_comm] using h
  · have h:=(TaoFivePrimes.rh_high_height_moment_arithmetic_block07 c hc j hj q hq).symm
    simpa only [wordRow,RHHighAllMomentWords.blocks,RHHighFFTArithmeticBase.decode,RHHighFFTArithmeticBase.fieldBase,
      RHHighFFTArithmeticBase.bias,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,Nat.mul_comm] using h
  · have h:=(TaoFivePrimes.rh_high_height_moment_arithmetic_block08 c hc j hj q hq).symm
    simpa only [wordRow,RHHighAllMomentWords.blocks,RHHighFFTArithmeticBase.decode,RHHighFFTArithmeticBase.fieldBase,
      RHHighFFTArithmeticBase.bias,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,Nat.mul_comm] using h
  · have h:=(TaoFivePrimes.rh_high_height_moment_arithmetic_block09 c hc j hj q hq).symm
    simpa only [wordRow,RHHighAllMomentWords.blocks,RHHighFFTArithmeticBase.decode,RHHighFFTArithmeticBase.fieldBase,
      RHHighFFTArithmeticBase.bias,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,Nat.mul_comm] using h
  · have h:=(TaoFivePrimes.rh_high_height_moment_arithmetic_block10 c hc j hj q hq).symm
    simpa only [wordRow,RHHighAllMomentWords.blocks,RHHighFFTArithmeticBase.decode,RHHighFFTArithmeticBase.fieldBase,
      RHHighFFTArithmeticBase.bias,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,Nat.mul_comm] using h
  · have h:=(TaoFivePrimes.rh_high_height_moment_arithmetic_block11 c hc j hj q hq).symm
    simpa only [wordRow,RHHighAllMomentWords.blocks,RHHighFFTArithmeticBase.decode,RHHighFFTArithmeticBase.fieldBase,
      RHHighFFTArithmeticBase.bias,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,Nat.mul_comm] using h
  · have h:=(TaoFivePrimes.rh_high_height_moment_arithmetic_block12 c hc j hj q hq).symm
    simpa only [wordRow,RHHighAllMomentWords.blocks,RHHighFFTArithmeticBase.decode,RHHighFFTArithmeticBase.fieldBase,
      RHHighFFTArithmeticBase.bias,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,Nat.mul_comm] using h
  · have h:=(TaoFivePrimes.rh_high_height_moment_arithmetic_block13 c hc j hj q hq).symm
    simpa only [wordRow,RHHighAllMomentWords.blocks,RHHighFFTArithmeticBase.decode,RHHighFFTArithmeticBase.fieldBase,
      RHHighFFTArithmeticBase.bias,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,Nat.mul_comm] using h
  · have h:=(TaoFivePrimes.rh_high_height_moment_arithmetic_block14 c hc j hj q hq).symm
    simpa only [wordRow,RHHighAllMomentWords.blocks,RHHighFFTArithmeticBase.decode,RHHighFFTArithmeticBase.fieldBase,
      RHHighFFTArithmeticBase.bias,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,Nat.mul_comm] using h
  · have h:=(TaoFivePrimes.rh_high_height_moment_arithmetic_block15 c hc j hj q hq).symm
    simpa only [wordRow,RHHighAllMomentWords.blocks,RHHighFFTArithmeticBase.decode,RHHighFFTArithmeticBase.fieldBase,
      RHHighFFTArithmeticBase.bias,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,Nat.mul_comm] using h
  · have h:=(TaoFivePrimes.rh_high_height_moment_arithmetic_block16 c hc j hj q hq).symm
    simpa only [wordRow,RHHighAllMomentWords.blocks,RHHighFFTArithmeticBase.decode,RHHighFFTArithmeticBase.fieldBase,
      RHHighFFTArithmeticBase.bias,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,Nat.mul_comm] using h
  · have h:=(TaoFivePrimes.rh_high_height_moment_arithmetic_block17 c hc j hj q hq).symm
    simpa only [wordRow,RHHighAllMomentWords.blocks,RHHighFFTArithmeticBase.decode,RHHighFFTArithmeticBase.fieldBase,
      RHHighFFTArithmeticBase.bias,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,Nat.mul_comm] using h
  · have h:=(TaoFivePrimes.rh_high_height_moment_arithmetic_block18 c hc j hj q hq).symm
    simpa only [wordRow,RHHighAllMomentWords.blocks,RHHighFFTArithmeticBase.decode,RHHighFFTArithmeticBase.fieldBase,
      RHHighFFTArithmeticBase.bias,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,Nat.mul_comm] using h
  · have h:=(TaoFivePrimes.rh_high_height_moment_arithmetic_block19 c hc j hj q hq).symm
    simpa only [wordRow,RHHighAllMomentWords.blocks,RHHighFFTArithmeticBase.decode,RHHighFFTArithmeticBase.fieldBase,
      RHHighFFTArithmeticBase.bias,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,Nat.mul_comm] using h
  · have h:=(TaoFivePrimes.rh_high_height_moment_arithmetic_block20 c hc j hj q hq).symm
    simpa only [wordRow,RHHighAllMomentWords.blocks,RHHighFFTArithmeticBase.decode,RHHighFFTArithmeticBase.fieldBase,
      RHHighFFTArithmeticBase.bias,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,Nat.mul_comm] using h
  · have h:=(TaoFivePrimes.rh_high_height_moment_arithmetic_block21 c hc j hj q hq).symm
    simpa only [wordRow,RHHighAllMomentWords.blocks,RHHighFFTArithmeticBase.decode,RHHighFFTArithmeticBase.fieldBase,
      RHHighFFTArithmeticBase.bias,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,Nat.mul_comm] using h
  · have h:=(TaoFivePrimes.rh_high_height_moment_arithmetic_block22 c hc j hj q hq).symm
    simpa only [wordRow,RHHighAllMomentWords.blocks,RHHighFFTArithmeticBase.decode,RHHighFFTArithmeticBase.fieldBase,
      RHHighFFTArithmeticBase.bias,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,Nat.mul_comm] using h
  · have h:=(TaoFivePrimes.rh_high_height_moment_arithmetic_block23 c hc j hj q hq).symm
    simpa only [wordRow,RHHighAllMomentWords.blocks,RHHighFFTArithmeticBase.decode,RHHighFFTArithmeticBase.fieldBase,
      RHHighFFTArithmeticBase.bias,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,Nat.mul_comm] using h
  · have h:=(TaoFivePrimes.rh_high_height_moment_arithmetic_block24 c hc j hj q hq).symm
    simpa only [wordRow,RHHighAllMomentWords.blocks,RHHighFFTArithmeticBase.decode,RHHighFFTArithmeticBase.fieldBase,
      RHHighFFTArithmeticBase.bias,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,Nat.mul_comm] using h
  · have h:=(TaoFivePrimes.rh_high_height_moment_arithmetic_block25 c hc j hj q hq).symm
    simpa only [wordRow,RHHighAllMomentWords.blocks,RHHighFFTArithmeticBase.decode,RHHighFFTArithmeticBase.fieldBase,
      RHHighFFTArithmeticBase.bias,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,Nat.mul_comm] using h
  · have h:=(TaoFivePrimes.rh_high_height_moment_arithmetic_block26 c hc j hj q hq).symm
    simpa only [wordRow,RHHighAllMomentWords.blocks,RHHighFFTArithmeticBase.decode,RHHighFFTArithmeticBase.fieldBase,
      RHHighFFTArithmeticBase.bias,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,Nat.mul_comm] using h
  · have h:=(TaoFivePrimes.rh_high_height_moment_arithmetic_block27 c hc j hj q hq).symm
    simpa only [wordRow,RHHighAllMomentWords.blocks,RHHighFFTArithmeticBase.decode,RHHighFFTArithmeticBase.fieldBase,
      RHHighFFTArithmeticBase.bias,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,Nat.mul_comm] using h
  · have h:=(TaoFivePrimes.rh_high_height_moment_arithmetic_block28 c hc j hj q hq).symm
    simpa only [wordRow,RHHighAllMomentWords.blocks,RHHighFFTArithmeticBase.decode,RHHighFFTArithmeticBase.fieldBase,
      RHHighFFTArithmeticBase.bias,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,Nat.mul_comm] using h
  · have h:=(TaoFivePrimes.rh_high_height_moment_arithmetic_block29 c hc j hj q hq).symm
    simpa only [wordRow,RHHighAllMomentWords.blocks,RHHighFFTArithmeticBase.decode,RHHighFFTArithmeticBase.fieldBase,
      RHHighFFTArithmeticBase.bias,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,Nat.mul_comm] using h
  · have h:=(TaoFivePrimes.rh_high_height_moment_arithmetic_block30 c hc j hj q hq).symm
    simpa only [wordRow,RHHighAllMomentWords.blocks,RHHighFFTArithmeticBase.decode,RHHighFFTArithmeticBase.fieldBase,
      RHHighFFTArithmeticBase.bias,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,Nat.mul_comm] using h
  · have h:=(TaoFivePrimes.rh_high_height_moment_arithmetic_block31 c hc j hj q hq).symm
    simpa only [wordRow,RHHighAllMomentWords.blocks,RHHighFFTArithmeticBase.decode,RHHighFFTArithmeticBase.fieldBase,
      RHHighFFTArithmeticBase.bias,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,Nat.mul_comm] using h
end RHHighAllMomentArithmetic
theorem solution :
 ∀ i:Nat,i<16384 → ∀ k:Nat,k<26 →
 RHHighFFTArithmeticBase.decode (RHHighAllMomentWords.word i) k=
 RHHighMomentArithmetic.moment i (RHHighGammaArithmetic.compute i) k := by
 intro i hi k hk
 let b:=i/512
 let c:=i%512/16
 let j:=i%16
 have h:=RHHighAllMomentArithmetic.moment_words b c j k (by dsimp [b];omega) (by dsimp [c];omega) (by dsimp [j];omega) hk
 have he:512*b+16*c+j=i:=by dsimp [b,c,j];omega
 rw [he] at h
 exact h
