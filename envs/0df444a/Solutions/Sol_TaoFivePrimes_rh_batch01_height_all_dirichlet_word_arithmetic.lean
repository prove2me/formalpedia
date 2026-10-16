-- Prove2me | solution 1 for TaoFivePrimes.rh_batch01_height_all_dirichlet_word_arithmetic
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T22:08:28.340078+00:00
-- url     : https://prove2.me/submissions/8fcd6f5f-4450-41b0-85de-0e5230399ff1

import Mathlib
import Definitions.Def_TaoFivePrimes_RHBatch01AllDirichletWords
import Definitions.Def_TaoFivePrimes_RHBatch01DirichletArithmetic
import Definitions.Def_TaoFivePrimes_RHHighDirichletBinning
import Theorems.Thm_TaoFivePrimes_rh_batch01_height_dirichlet_arithmetic00
import Theorems.Thm_TaoFivePrimes_rh_batch01_height_dirichlet_arithmetic01
import Theorems.Thm_TaoFivePrimes_rh_batch01_height_dirichlet_arithmetic02
import Theorems.Thm_TaoFivePrimes_rh_batch01_height_dirichlet_arithmetic03
import Theorems.Thm_TaoFivePrimes_rh_batch01_height_dirichlet_arithmetic04
import Theorems.Thm_TaoFivePrimes_rh_batch01_height_dirichlet_arithmetic05
import Theorems.Thm_TaoFivePrimes_rh_batch01_height_dirichlet_arithmetic06
import Theorems.Thm_TaoFivePrimes_rh_batch01_height_dirichlet_arithmetic07
import Theorems.Thm_TaoFivePrimes_rh_batch01_height_dirichlet_arithmetic08
import Theorems.Thm_TaoFivePrimes_rh_batch01_height_dirichlet_arithmetic09
import Theorems.Thm_TaoFivePrimes_rh_batch01_height_dirichlet_arithmetic10
import Theorems.Thm_TaoFivePrimes_rh_batch01_height_dirichlet_arithmetic11
import Theorems.Thm_TaoFivePrimes_rh_batch01_height_dirichlet_arithmetic12
import Theorems.Thm_TaoFivePrimes_rh_batch01_height_dirichlet_arithmetic13
import Theorems.Thm_TaoFivePrimes_rh_batch01_height_dirichlet_arithmetic14
import Theorems.Thm_TaoFivePrimes_rh_batch01_height_dirichlet_arithmetic15
import Theorems.Thm_TaoFivePrimes_rh_batch01_height_dirichlet_arithmetic16
import Theorems.Thm_TaoFivePrimes_rh_batch01_height_dirichlet_arithmetic17
import Theorems.Thm_TaoFivePrimes_rh_batch01_height_dirichlet_arithmetic18
import Theorems.Thm_TaoFivePrimes_rh_batch01_height_dirichlet_arithmetic19
import Theorems.Thm_TaoFivePrimes_rh_batch01_height_dirichlet_arithmetic20
import Theorems.Thm_TaoFivePrimes_rh_batch01_height_dirichlet_arithmetic21
import Theorems.Thm_TaoFivePrimes_rh_batch01_height_dirichlet_arithmetic22
import Theorems.Thm_TaoFivePrimes_rh_batch01_height_dirichlet_arithmetic23
import Theorems.Thm_TaoFivePrimes_rh_batch01_height_dirichlet_arithmetic24
import Theorems.Thm_TaoFivePrimes_rh_batch01_height_dirichlet_arithmetic25
import Theorems.Thm_TaoFivePrimes_rh_batch01_height_dirichlet_arithmetic26
import Theorems.Thm_TaoFivePrimes_rh_batch01_height_dirichlet_arithmetic27
import Theorems.Thm_TaoFivePrimes_rh_batch01_height_dirichlet_arithmetic28
import Theorems.Thm_TaoFivePrimes_rh_batch01_height_dirichlet_arithmetic29
import Theorems.Thm_TaoFivePrimes_rh_batch01_height_dirichlet_arithmetic30
import Theorems.Thm_TaoFivePrimes_rh_batch01_height_dirichlet_arithmetic31
import Theorems.Thm_TaoFivePrimes_rh_batch01_height_dirichlet_arithmetic32
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace RHBatch01AllDirichletWords
lemma word_at (b c j : Nat) (hc:c<96) (hj:j<16) :
    word (1536*b+1+16*c+j)=
      (((((packets[b]?).getD [])[c/32]?).getD [])[16*(c%32)+j]?).getD 0 := by
  have hn:(1536*b+1+16*c+j)-1=1536*b+16*c+j:=by omega
  have hb:(1536*b+16*c+j)/1536=b:=by omega
  have hr:((1536*b+16*c+j)%1536)/512=c/32:=by omega
  have hi:(1536*b+16*c+j)%512=16*(c%32)+j:=by omega
  simp only [word,hn,hb,hr,hi]
end RHBatch01AllDirichletWords
set_option exponentiation.threshold 10000
set_option backward.isDefEq.respectTransparency false
theorem solution :
  ∀ n:Nat,1 ≤ n ∧ n≤50000 →
  let w:=RHBatch01AllDirichletWords.word n
  (RHBatch01DirichletArithmetic.compute n).gammaRe=RHHighDirichletBinning.field w 0 ∧
  (RHBatch01DirichletArithmetic.compute n).gammaIm=RHHighDirichletBinning.field w 1 ∧
  RHBatch01DirichletArithmetic.delta n=RHHighDirichletBinning.field w 2 ∧
  RHBatch01DirichletArithmetic.bin n=RHHighDirichletBinning.bin w := by
  intro n hn
  have hp480:(2:Nat)^480=(2^160)^3:=by decide +kernel
  let b:=(n-1)/1536
  let c:=((n-1)%1536)/16
  let j:=(n-1)%16
  have hb:b<33:=by dsimp [b];omega
  have hc:c<96:=by dsimp [c];omega
  have hj:j<16:=by dsimp [j];omega
  have he:1536*b+1+16*c+j=n:=by dsimp [b,c,j];omega
  have hw:=RHBatch01AllDirichletWords.word_at b c j hc hj
  rw [he] at hw
  interval_cases b
  · have hc':c<96:=by omega
    have h:=TaoFivePrimes.rh_batch01_height_dirichlet_arithmetic00 c hc' j hj
    have he':1+16*c+j=n:=by omega
    rw [he'] at h
    simp only [RHBatch01AllDirichletWords.packets,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some] at hw
    change (RHBatch01DirichletArithmetic.compute n).gammaRe=RHHighDirichletBinning.field (RHBatch01AllDirichletWords.word n) 0 ∧
      (RHBatch01DirichletArithmetic.compute n).gammaIm=RHHighDirichletBinning.field (RHBatch01AllDirichletWords.word n) 1 ∧
      RHBatch01DirichletArithmetic.delta n=RHHighDirichletBinning.field (RHBatch01AllDirichletWords.word n) 2 ∧
      RHBatch01DirichletArithmetic.bin n=RHHighDirichletBinning.bin (RHBatch01AllDirichletWords.word n)
    rw [hw]
    have ht:=And.intro h.2.2.2.1 (And.intro h.2.2.2.2.1 (And.intro h.2.2.2.2.2.1 h.2.2.2.2.2.2))
    simpa only [RHHighDirichletBinning.field,RHHighDirichletBinning.bin,Nat.mul_zero,Nat.mul_one,
      Nat.pow_zero,Nat.div_one,hp480,pow_mul] using ht
  · have hc':c<96:=by omega
    have h:=TaoFivePrimes.rh_batch01_height_dirichlet_arithmetic01 c hc' j hj
    have he':1537+16*c+j=n:=by omega
    rw [he'] at h
    simp only [RHBatch01AllDirichletWords.packets,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some] at hw
    change (RHBatch01DirichletArithmetic.compute n).gammaRe=RHHighDirichletBinning.field (RHBatch01AllDirichletWords.word n) 0 ∧
      (RHBatch01DirichletArithmetic.compute n).gammaIm=RHHighDirichletBinning.field (RHBatch01AllDirichletWords.word n) 1 ∧
      RHBatch01DirichletArithmetic.delta n=RHHighDirichletBinning.field (RHBatch01AllDirichletWords.word n) 2 ∧
      RHBatch01DirichletArithmetic.bin n=RHHighDirichletBinning.bin (RHBatch01AllDirichletWords.word n)
    rw [hw]
    have ht:=And.intro h.2.2.2.1 (And.intro h.2.2.2.2.1 (And.intro h.2.2.2.2.2.1 h.2.2.2.2.2.2))
    simpa only [RHHighDirichletBinning.field,RHHighDirichletBinning.bin,Nat.mul_zero,Nat.mul_one,
      Nat.pow_zero,Nat.div_one,hp480,pow_mul] using ht
  · have hc':c<96:=by omega
    have h:=TaoFivePrimes.rh_batch01_height_dirichlet_arithmetic02 c hc' j hj
    have he':3073+16*c+j=n:=by omega
    rw [he'] at h
    simp only [RHBatch01AllDirichletWords.packets,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some] at hw
    change (RHBatch01DirichletArithmetic.compute n).gammaRe=RHHighDirichletBinning.field (RHBatch01AllDirichletWords.word n) 0 ∧
      (RHBatch01DirichletArithmetic.compute n).gammaIm=RHHighDirichletBinning.field (RHBatch01AllDirichletWords.word n) 1 ∧
      RHBatch01DirichletArithmetic.delta n=RHHighDirichletBinning.field (RHBatch01AllDirichletWords.word n) 2 ∧
      RHBatch01DirichletArithmetic.bin n=RHHighDirichletBinning.bin (RHBatch01AllDirichletWords.word n)
    rw [hw]
    have ht:=And.intro h.2.2.2.1 (And.intro h.2.2.2.2.1 (And.intro h.2.2.2.2.2.1 h.2.2.2.2.2.2))
    simpa only [RHHighDirichletBinning.field,RHHighDirichletBinning.bin,Nat.mul_zero,Nat.mul_one,
      Nat.pow_zero,Nat.div_one,hp480,pow_mul] using ht
  · have hc':c<96:=by omega
    have h:=TaoFivePrimes.rh_batch01_height_dirichlet_arithmetic03 c hc' j hj
    have he':4609+16*c+j=n:=by omega
    rw [he'] at h
    simp only [RHBatch01AllDirichletWords.packets,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some] at hw
    change (RHBatch01DirichletArithmetic.compute n).gammaRe=RHHighDirichletBinning.field (RHBatch01AllDirichletWords.word n) 0 ∧
      (RHBatch01DirichletArithmetic.compute n).gammaIm=RHHighDirichletBinning.field (RHBatch01AllDirichletWords.word n) 1 ∧
      RHBatch01DirichletArithmetic.delta n=RHHighDirichletBinning.field (RHBatch01AllDirichletWords.word n) 2 ∧
      RHBatch01DirichletArithmetic.bin n=RHHighDirichletBinning.bin (RHBatch01AllDirichletWords.word n)
    rw [hw]
    have ht:=And.intro h.2.2.2.1 (And.intro h.2.2.2.2.1 (And.intro h.2.2.2.2.2.1 h.2.2.2.2.2.2))
    simpa only [RHHighDirichletBinning.field,RHHighDirichletBinning.bin,Nat.mul_zero,Nat.mul_one,
      Nat.pow_zero,Nat.div_one,hp480,pow_mul] using ht
  · have hc':c<96:=by omega
    have h:=TaoFivePrimes.rh_batch01_height_dirichlet_arithmetic04 c hc' j hj
    have he':6145+16*c+j=n:=by omega
    rw [he'] at h
    simp only [RHBatch01AllDirichletWords.packets,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some] at hw
    change (RHBatch01DirichletArithmetic.compute n).gammaRe=RHHighDirichletBinning.field (RHBatch01AllDirichletWords.word n) 0 ∧
      (RHBatch01DirichletArithmetic.compute n).gammaIm=RHHighDirichletBinning.field (RHBatch01AllDirichletWords.word n) 1 ∧
      RHBatch01DirichletArithmetic.delta n=RHHighDirichletBinning.field (RHBatch01AllDirichletWords.word n) 2 ∧
      RHBatch01DirichletArithmetic.bin n=RHHighDirichletBinning.bin (RHBatch01AllDirichletWords.word n)
    rw [hw]
    have ht:=And.intro h.2.2.2.1 (And.intro h.2.2.2.2.1 (And.intro h.2.2.2.2.2.1 h.2.2.2.2.2.2))
    simpa only [RHHighDirichletBinning.field,RHHighDirichletBinning.bin,Nat.mul_zero,Nat.mul_one,
      Nat.pow_zero,Nat.div_one,hp480,pow_mul] using ht
  · have hc':c<96:=by omega
    have h:=TaoFivePrimes.rh_batch01_height_dirichlet_arithmetic05 c hc' j hj
    have he':7681+16*c+j=n:=by omega
    rw [he'] at h
    simp only [RHBatch01AllDirichletWords.packets,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some] at hw
    change (RHBatch01DirichletArithmetic.compute n).gammaRe=RHHighDirichletBinning.field (RHBatch01AllDirichletWords.word n) 0 ∧
      (RHBatch01DirichletArithmetic.compute n).gammaIm=RHHighDirichletBinning.field (RHBatch01AllDirichletWords.word n) 1 ∧
      RHBatch01DirichletArithmetic.delta n=RHHighDirichletBinning.field (RHBatch01AllDirichletWords.word n) 2 ∧
      RHBatch01DirichletArithmetic.bin n=RHHighDirichletBinning.bin (RHBatch01AllDirichletWords.word n)
    rw [hw]
    have ht:=And.intro h.2.2.2.1 (And.intro h.2.2.2.2.1 (And.intro h.2.2.2.2.2.1 h.2.2.2.2.2.2))
    simpa only [RHHighDirichletBinning.field,RHHighDirichletBinning.bin,Nat.mul_zero,Nat.mul_one,
      Nat.pow_zero,Nat.div_one,hp480,pow_mul] using ht
  · have hc':c<96:=by omega
    have h:=TaoFivePrimes.rh_batch01_height_dirichlet_arithmetic06 c hc' j hj
    have he':9217+16*c+j=n:=by omega
    rw [he'] at h
    simp only [RHBatch01AllDirichletWords.packets,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some] at hw
    change (RHBatch01DirichletArithmetic.compute n).gammaRe=RHHighDirichletBinning.field (RHBatch01AllDirichletWords.word n) 0 ∧
      (RHBatch01DirichletArithmetic.compute n).gammaIm=RHHighDirichletBinning.field (RHBatch01AllDirichletWords.word n) 1 ∧
      RHBatch01DirichletArithmetic.delta n=RHHighDirichletBinning.field (RHBatch01AllDirichletWords.word n) 2 ∧
      RHBatch01DirichletArithmetic.bin n=RHHighDirichletBinning.bin (RHBatch01AllDirichletWords.word n)
    rw [hw]
    have ht:=And.intro h.2.2.2.1 (And.intro h.2.2.2.2.1 (And.intro h.2.2.2.2.2.1 h.2.2.2.2.2.2))
    simpa only [RHHighDirichletBinning.field,RHHighDirichletBinning.bin,Nat.mul_zero,Nat.mul_one,
      Nat.pow_zero,Nat.div_one,hp480,pow_mul] using ht
  · have hc':c<96:=by omega
    have h:=TaoFivePrimes.rh_batch01_height_dirichlet_arithmetic07 c hc' j hj
    have he':10753+16*c+j=n:=by omega
    rw [he'] at h
    simp only [RHBatch01AllDirichletWords.packets,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some] at hw
    change (RHBatch01DirichletArithmetic.compute n).gammaRe=RHHighDirichletBinning.field (RHBatch01AllDirichletWords.word n) 0 ∧
      (RHBatch01DirichletArithmetic.compute n).gammaIm=RHHighDirichletBinning.field (RHBatch01AllDirichletWords.word n) 1 ∧
      RHBatch01DirichletArithmetic.delta n=RHHighDirichletBinning.field (RHBatch01AllDirichletWords.word n) 2 ∧
      RHBatch01DirichletArithmetic.bin n=RHHighDirichletBinning.bin (RHBatch01AllDirichletWords.word n)
    rw [hw]
    have ht:=And.intro h.2.2.2.1 (And.intro h.2.2.2.2.1 (And.intro h.2.2.2.2.2.1 h.2.2.2.2.2.2))
    simpa only [RHHighDirichletBinning.field,RHHighDirichletBinning.bin,Nat.mul_zero,Nat.mul_one,
      Nat.pow_zero,Nat.div_one,hp480,pow_mul] using ht
  · have hc':c<96:=by omega
    have h:=TaoFivePrimes.rh_batch01_height_dirichlet_arithmetic08 c hc' j hj
    have he':12289+16*c+j=n:=by omega
    rw [he'] at h
    simp only [RHBatch01AllDirichletWords.packets,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some] at hw
    change (RHBatch01DirichletArithmetic.compute n).gammaRe=RHHighDirichletBinning.field (RHBatch01AllDirichletWords.word n) 0 ∧
      (RHBatch01DirichletArithmetic.compute n).gammaIm=RHHighDirichletBinning.field (RHBatch01AllDirichletWords.word n) 1 ∧
      RHBatch01DirichletArithmetic.delta n=RHHighDirichletBinning.field (RHBatch01AllDirichletWords.word n) 2 ∧
      RHBatch01DirichletArithmetic.bin n=RHHighDirichletBinning.bin (RHBatch01AllDirichletWords.word n)
    rw [hw]
    have ht:=And.intro h.2.2.2.1 (And.intro h.2.2.2.2.1 (And.intro h.2.2.2.2.2.1 h.2.2.2.2.2.2))
    simpa only [RHHighDirichletBinning.field,RHHighDirichletBinning.bin,Nat.mul_zero,Nat.mul_one,
      Nat.pow_zero,Nat.div_one,hp480,pow_mul] using ht
  · have hc':c<96:=by omega
    have h:=TaoFivePrimes.rh_batch01_height_dirichlet_arithmetic09 c hc' j hj
    have he':13825+16*c+j=n:=by omega
    rw [he'] at h
    simp only [RHBatch01AllDirichletWords.packets,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some] at hw
    change (RHBatch01DirichletArithmetic.compute n).gammaRe=RHHighDirichletBinning.field (RHBatch01AllDirichletWords.word n) 0 ∧
      (RHBatch01DirichletArithmetic.compute n).gammaIm=RHHighDirichletBinning.field (RHBatch01AllDirichletWords.word n) 1 ∧
      RHBatch01DirichletArithmetic.delta n=RHHighDirichletBinning.field (RHBatch01AllDirichletWords.word n) 2 ∧
      RHBatch01DirichletArithmetic.bin n=RHHighDirichletBinning.bin (RHBatch01AllDirichletWords.word n)
    rw [hw]
    have ht:=And.intro h.2.2.2.1 (And.intro h.2.2.2.2.1 (And.intro h.2.2.2.2.2.1 h.2.2.2.2.2.2))
    simpa only [RHHighDirichletBinning.field,RHHighDirichletBinning.bin,Nat.mul_zero,Nat.mul_one,
      Nat.pow_zero,Nat.div_one,hp480,pow_mul] using ht
  · have hc':c<96:=by omega
    have h:=TaoFivePrimes.rh_batch01_height_dirichlet_arithmetic10 c hc' j hj
    have he':15361+16*c+j=n:=by omega
    rw [he'] at h
    simp only [RHBatch01AllDirichletWords.packets,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some] at hw
    change (RHBatch01DirichletArithmetic.compute n).gammaRe=RHHighDirichletBinning.field (RHBatch01AllDirichletWords.word n) 0 ∧
      (RHBatch01DirichletArithmetic.compute n).gammaIm=RHHighDirichletBinning.field (RHBatch01AllDirichletWords.word n) 1 ∧
      RHBatch01DirichletArithmetic.delta n=RHHighDirichletBinning.field (RHBatch01AllDirichletWords.word n) 2 ∧
      RHBatch01DirichletArithmetic.bin n=RHHighDirichletBinning.bin (RHBatch01AllDirichletWords.word n)
    rw [hw]
    have ht:=And.intro h.2.2.2.1 (And.intro h.2.2.2.2.1 (And.intro h.2.2.2.2.2.1 h.2.2.2.2.2.2))
    simpa only [RHHighDirichletBinning.field,RHHighDirichletBinning.bin,Nat.mul_zero,Nat.mul_one,
      Nat.pow_zero,Nat.div_one,hp480,pow_mul] using ht
  · have hc':c<96:=by omega
    have h:=TaoFivePrimes.rh_batch01_height_dirichlet_arithmetic11 c hc' j hj
    have he':16897+16*c+j=n:=by omega
    rw [he'] at h
    simp only [RHBatch01AllDirichletWords.packets,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some] at hw
    change (RHBatch01DirichletArithmetic.compute n).gammaRe=RHHighDirichletBinning.field (RHBatch01AllDirichletWords.word n) 0 ∧
      (RHBatch01DirichletArithmetic.compute n).gammaIm=RHHighDirichletBinning.field (RHBatch01AllDirichletWords.word n) 1 ∧
      RHBatch01DirichletArithmetic.delta n=RHHighDirichletBinning.field (RHBatch01AllDirichletWords.word n) 2 ∧
      RHBatch01DirichletArithmetic.bin n=RHHighDirichletBinning.bin (RHBatch01AllDirichletWords.word n)
    rw [hw]
    have ht:=And.intro h.2.2.2.1 (And.intro h.2.2.2.2.1 (And.intro h.2.2.2.2.2.1 h.2.2.2.2.2.2))
    simpa only [RHHighDirichletBinning.field,RHHighDirichletBinning.bin,Nat.mul_zero,Nat.mul_one,
      Nat.pow_zero,Nat.div_one,hp480,pow_mul] using ht
  · have hc':c<96:=by omega
    have h:=TaoFivePrimes.rh_batch01_height_dirichlet_arithmetic12 c hc' j hj
    have he':18433+16*c+j=n:=by omega
    rw [he'] at h
    simp only [RHBatch01AllDirichletWords.packets,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some] at hw
    change (RHBatch01DirichletArithmetic.compute n).gammaRe=RHHighDirichletBinning.field (RHBatch01AllDirichletWords.word n) 0 ∧
      (RHBatch01DirichletArithmetic.compute n).gammaIm=RHHighDirichletBinning.field (RHBatch01AllDirichletWords.word n) 1 ∧
      RHBatch01DirichletArithmetic.delta n=RHHighDirichletBinning.field (RHBatch01AllDirichletWords.word n) 2 ∧
      RHBatch01DirichletArithmetic.bin n=RHHighDirichletBinning.bin (RHBatch01AllDirichletWords.word n)
    rw [hw]
    have ht:=And.intro h.2.2.2.1 (And.intro h.2.2.2.2.1 (And.intro h.2.2.2.2.2.1 h.2.2.2.2.2.2))
    simpa only [RHHighDirichletBinning.field,RHHighDirichletBinning.bin,Nat.mul_zero,Nat.mul_one,
      Nat.pow_zero,Nat.div_one,hp480,pow_mul] using ht
  · have hc':c<96:=by omega
    have h:=TaoFivePrimes.rh_batch01_height_dirichlet_arithmetic13 c hc' j hj
    have he':19969+16*c+j=n:=by omega
    rw [he'] at h
    simp only [RHBatch01AllDirichletWords.packets,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some] at hw
    change (RHBatch01DirichletArithmetic.compute n).gammaRe=RHHighDirichletBinning.field (RHBatch01AllDirichletWords.word n) 0 ∧
      (RHBatch01DirichletArithmetic.compute n).gammaIm=RHHighDirichletBinning.field (RHBatch01AllDirichletWords.word n) 1 ∧
      RHBatch01DirichletArithmetic.delta n=RHHighDirichletBinning.field (RHBatch01AllDirichletWords.word n) 2 ∧
      RHBatch01DirichletArithmetic.bin n=RHHighDirichletBinning.bin (RHBatch01AllDirichletWords.word n)
    rw [hw]
    have ht:=And.intro h.2.2.2.1 (And.intro h.2.2.2.2.1 (And.intro h.2.2.2.2.2.1 h.2.2.2.2.2.2))
    simpa only [RHHighDirichletBinning.field,RHHighDirichletBinning.bin,Nat.mul_zero,Nat.mul_one,
      Nat.pow_zero,Nat.div_one,hp480,pow_mul] using ht
  · have hc':c<96:=by omega
    have h:=TaoFivePrimes.rh_batch01_height_dirichlet_arithmetic14 c hc' j hj
    have he':21505+16*c+j=n:=by omega
    rw [he'] at h
    simp only [RHBatch01AllDirichletWords.packets,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some] at hw
    change (RHBatch01DirichletArithmetic.compute n).gammaRe=RHHighDirichletBinning.field (RHBatch01AllDirichletWords.word n) 0 ∧
      (RHBatch01DirichletArithmetic.compute n).gammaIm=RHHighDirichletBinning.field (RHBatch01AllDirichletWords.word n) 1 ∧
      RHBatch01DirichletArithmetic.delta n=RHHighDirichletBinning.field (RHBatch01AllDirichletWords.word n) 2 ∧
      RHBatch01DirichletArithmetic.bin n=RHHighDirichletBinning.bin (RHBatch01AllDirichletWords.word n)
    rw [hw]
    have ht:=And.intro h.2.2.2.1 (And.intro h.2.2.2.2.1 (And.intro h.2.2.2.2.2.1 h.2.2.2.2.2.2))
    simpa only [RHHighDirichletBinning.field,RHHighDirichletBinning.bin,Nat.mul_zero,Nat.mul_one,
      Nat.pow_zero,Nat.div_one,hp480,pow_mul] using ht
  · have hc':c<96:=by omega
    have h:=TaoFivePrimes.rh_batch01_height_dirichlet_arithmetic15 c hc' j hj
    have he':23041+16*c+j=n:=by omega
    rw [he'] at h
    simp only [RHBatch01AllDirichletWords.packets,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some] at hw
    change (RHBatch01DirichletArithmetic.compute n).gammaRe=RHHighDirichletBinning.field (RHBatch01AllDirichletWords.word n) 0 ∧
      (RHBatch01DirichletArithmetic.compute n).gammaIm=RHHighDirichletBinning.field (RHBatch01AllDirichletWords.word n) 1 ∧
      RHBatch01DirichletArithmetic.delta n=RHHighDirichletBinning.field (RHBatch01AllDirichletWords.word n) 2 ∧
      RHBatch01DirichletArithmetic.bin n=RHHighDirichletBinning.bin (RHBatch01AllDirichletWords.word n)
    rw [hw]
    have ht:=And.intro h.2.2.2.1 (And.intro h.2.2.2.2.1 (And.intro h.2.2.2.2.2.1 h.2.2.2.2.2.2))
    simpa only [RHHighDirichletBinning.field,RHHighDirichletBinning.bin,Nat.mul_zero,Nat.mul_one,
      Nat.pow_zero,Nat.div_one,hp480,pow_mul] using ht
  · have hc':c<96:=by omega
    have h:=TaoFivePrimes.rh_batch01_height_dirichlet_arithmetic16 c hc' j hj
    have he':24577+16*c+j=n:=by omega
    rw [he'] at h
    simp only [RHBatch01AllDirichletWords.packets,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some] at hw
    change (RHBatch01DirichletArithmetic.compute n).gammaRe=RHHighDirichletBinning.field (RHBatch01AllDirichletWords.word n) 0 ∧
      (RHBatch01DirichletArithmetic.compute n).gammaIm=RHHighDirichletBinning.field (RHBatch01AllDirichletWords.word n) 1 ∧
      RHBatch01DirichletArithmetic.delta n=RHHighDirichletBinning.field (RHBatch01AllDirichletWords.word n) 2 ∧
      RHBatch01DirichletArithmetic.bin n=RHHighDirichletBinning.bin (RHBatch01AllDirichletWords.word n)
    rw [hw]
    have ht:=And.intro h.2.2.2.1 (And.intro h.2.2.2.2.1 (And.intro h.2.2.2.2.2.1 h.2.2.2.2.2.2))
    simpa only [RHHighDirichletBinning.field,RHHighDirichletBinning.bin,Nat.mul_zero,Nat.mul_one,
      Nat.pow_zero,Nat.div_one,hp480,pow_mul] using ht
  · have hc':c<96:=by omega
    have h:=TaoFivePrimes.rh_batch01_height_dirichlet_arithmetic17 c hc' j hj
    have he':26113+16*c+j=n:=by omega
    rw [he'] at h
    simp only [RHBatch01AllDirichletWords.packets,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some] at hw
    change (RHBatch01DirichletArithmetic.compute n).gammaRe=RHHighDirichletBinning.field (RHBatch01AllDirichletWords.word n) 0 ∧
      (RHBatch01DirichletArithmetic.compute n).gammaIm=RHHighDirichletBinning.field (RHBatch01AllDirichletWords.word n) 1 ∧
      RHBatch01DirichletArithmetic.delta n=RHHighDirichletBinning.field (RHBatch01AllDirichletWords.word n) 2 ∧
      RHBatch01DirichletArithmetic.bin n=RHHighDirichletBinning.bin (RHBatch01AllDirichletWords.word n)
    rw [hw]
    have ht:=And.intro h.2.2.2.1 (And.intro h.2.2.2.2.1 (And.intro h.2.2.2.2.2.1 h.2.2.2.2.2.2))
    simpa only [RHHighDirichletBinning.field,RHHighDirichletBinning.bin,Nat.mul_zero,Nat.mul_one,
      Nat.pow_zero,Nat.div_one,hp480,pow_mul] using ht
  · have hc':c<96:=by omega
    have h:=TaoFivePrimes.rh_batch01_height_dirichlet_arithmetic18 c hc' j hj
    have he':27649+16*c+j=n:=by omega
    rw [he'] at h
    simp only [RHBatch01AllDirichletWords.packets,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some] at hw
    change (RHBatch01DirichletArithmetic.compute n).gammaRe=RHHighDirichletBinning.field (RHBatch01AllDirichletWords.word n) 0 ∧
      (RHBatch01DirichletArithmetic.compute n).gammaIm=RHHighDirichletBinning.field (RHBatch01AllDirichletWords.word n) 1 ∧
      RHBatch01DirichletArithmetic.delta n=RHHighDirichletBinning.field (RHBatch01AllDirichletWords.word n) 2 ∧
      RHBatch01DirichletArithmetic.bin n=RHHighDirichletBinning.bin (RHBatch01AllDirichletWords.word n)
    rw [hw]
    have ht:=And.intro h.2.2.2.1 (And.intro h.2.2.2.2.1 (And.intro h.2.2.2.2.2.1 h.2.2.2.2.2.2))
    simpa only [RHHighDirichletBinning.field,RHHighDirichletBinning.bin,Nat.mul_zero,Nat.mul_one,
      Nat.pow_zero,Nat.div_one,hp480,pow_mul] using ht
  · have hc':c<96:=by omega
    have h:=TaoFivePrimes.rh_batch01_height_dirichlet_arithmetic19 c hc' j hj
    have he':29185+16*c+j=n:=by omega
    rw [he'] at h
    simp only [RHBatch01AllDirichletWords.packets,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some] at hw
    change (RHBatch01DirichletArithmetic.compute n).gammaRe=RHHighDirichletBinning.field (RHBatch01AllDirichletWords.word n) 0 ∧
      (RHBatch01DirichletArithmetic.compute n).gammaIm=RHHighDirichletBinning.field (RHBatch01AllDirichletWords.word n) 1 ∧
      RHBatch01DirichletArithmetic.delta n=RHHighDirichletBinning.field (RHBatch01AllDirichletWords.word n) 2 ∧
      RHBatch01DirichletArithmetic.bin n=RHHighDirichletBinning.bin (RHBatch01AllDirichletWords.word n)
    rw [hw]
    have ht:=And.intro h.2.2.2.1 (And.intro h.2.2.2.2.1 (And.intro h.2.2.2.2.2.1 h.2.2.2.2.2.2))
    simpa only [RHHighDirichletBinning.field,RHHighDirichletBinning.bin,Nat.mul_zero,Nat.mul_one,
      Nat.pow_zero,Nat.div_one,hp480,pow_mul] using ht
  · have hc':c<96:=by omega
    have h:=TaoFivePrimes.rh_batch01_height_dirichlet_arithmetic20 c hc' j hj
    have he':30721+16*c+j=n:=by omega
    rw [he'] at h
    simp only [RHBatch01AllDirichletWords.packets,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some] at hw
    change (RHBatch01DirichletArithmetic.compute n).gammaRe=RHHighDirichletBinning.field (RHBatch01AllDirichletWords.word n) 0 ∧
      (RHBatch01DirichletArithmetic.compute n).gammaIm=RHHighDirichletBinning.field (RHBatch01AllDirichletWords.word n) 1 ∧
      RHBatch01DirichletArithmetic.delta n=RHHighDirichletBinning.field (RHBatch01AllDirichletWords.word n) 2 ∧
      RHBatch01DirichletArithmetic.bin n=RHHighDirichletBinning.bin (RHBatch01AllDirichletWords.word n)
    rw [hw]
    have ht:=And.intro h.2.2.2.1 (And.intro h.2.2.2.2.1 (And.intro h.2.2.2.2.2.1 h.2.2.2.2.2.2))
    simpa only [RHHighDirichletBinning.field,RHHighDirichletBinning.bin,Nat.mul_zero,Nat.mul_one,
      Nat.pow_zero,Nat.div_one,hp480,pow_mul] using ht
  · have hc':c<96:=by omega
    have h:=TaoFivePrimes.rh_batch01_height_dirichlet_arithmetic21 c hc' j hj
    have he':32257+16*c+j=n:=by omega
    rw [he'] at h
    simp only [RHBatch01AllDirichletWords.packets,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some] at hw
    change (RHBatch01DirichletArithmetic.compute n).gammaRe=RHHighDirichletBinning.field (RHBatch01AllDirichletWords.word n) 0 ∧
      (RHBatch01DirichletArithmetic.compute n).gammaIm=RHHighDirichletBinning.field (RHBatch01AllDirichletWords.word n) 1 ∧
      RHBatch01DirichletArithmetic.delta n=RHHighDirichletBinning.field (RHBatch01AllDirichletWords.word n) 2 ∧
      RHBatch01DirichletArithmetic.bin n=RHHighDirichletBinning.bin (RHBatch01AllDirichletWords.word n)
    rw [hw]
    have ht:=And.intro h.2.2.2.1 (And.intro h.2.2.2.2.1 (And.intro h.2.2.2.2.2.1 h.2.2.2.2.2.2))
    simpa only [RHHighDirichletBinning.field,RHHighDirichletBinning.bin,Nat.mul_zero,Nat.mul_one,
      Nat.pow_zero,Nat.div_one,hp480,pow_mul] using ht
  · have hc':c<96:=by omega
    have h:=TaoFivePrimes.rh_batch01_height_dirichlet_arithmetic22 c hc' j hj
    have he':33793+16*c+j=n:=by omega
    rw [he'] at h
    simp only [RHBatch01AllDirichletWords.packets,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some] at hw
    change (RHBatch01DirichletArithmetic.compute n).gammaRe=RHHighDirichletBinning.field (RHBatch01AllDirichletWords.word n) 0 ∧
      (RHBatch01DirichletArithmetic.compute n).gammaIm=RHHighDirichletBinning.field (RHBatch01AllDirichletWords.word n) 1 ∧
      RHBatch01DirichletArithmetic.delta n=RHHighDirichletBinning.field (RHBatch01AllDirichletWords.word n) 2 ∧
      RHBatch01DirichletArithmetic.bin n=RHHighDirichletBinning.bin (RHBatch01AllDirichletWords.word n)
    rw [hw]
    have ht:=And.intro h.2.2.2.1 (And.intro h.2.2.2.2.1 (And.intro h.2.2.2.2.2.1 h.2.2.2.2.2.2))
    simpa only [RHHighDirichletBinning.field,RHHighDirichletBinning.bin,Nat.mul_zero,Nat.mul_one,
      Nat.pow_zero,Nat.div_one,hp480,pow_mul] using ht
  · have hc':c<96:=by omega
    have h:=TaoFivePrimes.rh_batch01_height_dirichlet_arithmetic23 c hc' j hj
    have he':35329+16*c+j=n:=by omega
    rw [he'] at h
    simp only [RHBatch01AllDirichletWords.packets,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some] at hw
    change (RHBatch01DirichletArithmetic.compute n).gammaRe=RHHighDirichletBinning.field (RHBatch01AllDirichletWords.word n) 0 ∧
      (RHBatch01DirichletArithmetic.compute n).gammaIm=RHHighDirichletBinning.field (RHBatch01AllDirichletWords.word n) 1 ∧
      RHBatch01DirichletArithmetic.delta n=RHHighDirichletBinning.field (RHBatch01AllDirichletWords.word n) 2 ∧
      RHBatch01DirichletArithmetic.bin n=RHHighDirichletBinning.bin (RHBatch01AllDirichletWords.word n)
    rw [hw]
    have ht:=And.intro h.2.2.2.1 (And.intro h.2.2.2.2.1 (And.intro h.2.2.2.2.2.1 h.2.2.2.2.2.2))
    simpa only [RHHighDirichletBinning.field,RHHighDirichletBinning.bin,Nat.mul_zero,Nat.mul_one,
      Nat.pow_zero,Nat.div_one,hp480,pow_mul] using ht
  · have hc':c<96:=by omega
    have h:=TaoFivePrimes.rh_batch01_height_dirichlet_arithmetic24 c hc' j hj
    have he':36865+16*c+j=n:=by omega
    rw [he'] at h
    simp only [RHBatch01AllDirichletWords.packets,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some] at hw
    change (RHBatch01DirichletArithmetic.compute n).gammaRe=RHHighDirichletBinning.field (RHBatch01AllDirichletWords.word n) 0 ∧
      (RHBatch01DirichletArithmetic.compute n).gammaIm=RHHighDirichletBinning.field (RHBatch01AllDirichletWords.word n) 1 ∧
      RHBatch01DirichletArithmetic.delta n=RHHighDirichletBinning.field (RHBatch01AllDirichletWords.word n) 2 ∧
      RHBatch01DirichletArithmetic.bin n=RHHighDirichletBinning.bin (RHBatch01AllDirichletWords.word n)
    rw [hw]
    have ht:=And.intro h.2.2.2.1 (And.intro h.2.2.2.2.1 (And.intro h.2.2.2.2.2.1 h.2.2.2.2.2.2))
    simpa only [RHHighDirichletBinning.field,RHHighDirichletBinning.bin,Nat.mul_zero,Nat.mul_one,
      Nat.pow_zero,Nat.div_one,hp480,pow_mul] using ht
  · have hc':c<96:=by omega
    have h:=TaoFivePrimes.rh_batch01_height_dirichlet_arithmetic25 c hc' j hj
    have he':38401+16*c+j=n:=by omega
    rw [he'] at h
    simp only [RHBatch01AllDirichletWords.packets,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some] at hw
    change (RHBatch01DirichletArithmetic.compute n).gammaRe=RHHighDirichletBinning.field (RHBatch01AllDirichletWords.word n) 0 ∧
      (RHBatch01DirichletArithmetic.compute n).gammaIm=RHHighDirichletBinning.field (RHBatch01AllDirichletWords.word n) 1 ∧
      RHBatch01DirichletArithmetic.delta n=RHHighDirichletBinning.field (RHBatch01AllDirichletWords.word n) 2 ∧
      RHBatch01DirichletArithmetic.bin n=RHHighDirichletBinning.bin (RHBatch01AllDirichletWords.word n)
    rw [hw]
    have ht:=And.intro h.2.2.2.1 (And.intro h.2.2.2.2.1 (And.intro h.2.2.2.2.2.1 h.2.2.2.2.2.2))
    simpa only [RHHighDirichletBinning.field,RHHighDirichletBinning.bin,Nat.mul_zero,Nat.mul_one,
      Nat.pow_zero,Nat.div_one,hp480,pow_mul] using ht
  · have hc':c<96:=by omega
    have h:=TaoFivePrimes.rh_batch01_height_dirichlet_arithmetic26 c hc' j hj
    have he':39937+16*c+j=n:=by omega
    rw [he'] at h
    simp only [RHBatch01AllDirichletWords.packets,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some] at hw
    change (RHBatch01DirichletArithmetic.compute n).gammaRe=RHHighDirichletBinning.field (RHBatch01AllDirichletWords.word n) 0 ∧
      (RHBatch01DirichletArithmetic.compute n).gammaIm=RHHighDirichletBinning.field (RHBatch01AllDirichletWords.word n) 1 ∧
      RHBatch01DirichletArithmetic.delta n=RHHighDirichletBinning.field (RHBatch01AllDirichletWords.word n) 2 ∧
      RHBatch01DirichletArithmetic.bin n=RHHighDirichletBinning.bin (RHBatch01AllDirichletWords.word n)
    rw [hw]
    have ht:=And.intro h.2.2.2.1 (And.intro h.2.2.2.2.1 (And.intro h.2.2.2.2.2.1 h.2.2.2.2.2.2))
    simpa only [RHHighDirichletBinning.field,RHHighDirichletBinning.bin,Nat.mul_zero,Nat.mul_one,
      Nat.pow_zero,Nat.div_one,hp480,pow_mul] using ht
  · have hc':c<96:=by omega
    have h:=TaoFivePrimes.rh_batch01_height_dirichlet_arithmetic27 c hc' j hj
    have he':41473+16*c+j=n:=by omega
    rw [he'] at h
    simp only [RHBatch01AllDirichletWords.packets,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some] at hw
    change (RHBatch01DirichletArithmetic.compute n).gammaRe=RHHighDirichletBinning.field (RHBatch01AllDirichletWords.word n) 0 ∧
      (RHBatch01DirichletArithmetic.compute n).gammaIm=RHHighDirichletBinning.field (RHBatch01AllDirichletWords.word n) 1 ∧
      RHBatch01DirichletArithmetic.delta n=RHHighDirichletBinning.field (RHBatch01AllDirichletWords.word n) 2 ∧
      RHBatch01DirichletArithmetic.bin n=RHHighDirichletBinning.bin (RHBatch01AllDirichletWords.word n)
    rw [hw]
    have ht:=And.intro h.2.2.2.1 (And.intro h.2.2.2.2.1 (And.intro h.2.2.2.2.2.1 h.2.2.2.2.2.2))
    simpa only [RHHighDirichletBinning.field,RHHighDirichletBinning.bin,Nat.mul_zero,Nat.mul_one,
      Nat.pow_zero,Nat.div_one,hp480,pow_mul] using ht
  · have hc':c<96:=by omega
    have h:=TaoFivePrimes.rh_batch01_height_dirichlet_arithmetic28 c hc' j hj
    have he':43009+16*c+j=n:=by omega
    rw [he'] at h
    simp only [RHBatch01AllDirichletWords.packets,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some] at hw
    change (RHBatch01DirichletArithmetic.compute n).gammaRe=RHHighDirichletBinning.field (RHBatch01AllDirichletWords.word n) 0 ∧
      (RHBatch01DirichletArithmetic.compute n).gammaIm=RHHighDirichletBinning.field (RHBatch01AllDirichletWords.word n) 1 ∧
      RHBatch01DirichletArithmetic.delta n=RHHighDirichletBinning.field (RHBatch01AllDirichletWords.word n) 2 ∧
      RHBatch01DirichletArithmetic.bin n=RHHighDirichletBinning.bin (RHBatch01AllDirichletWords.word n)
    rw [hw]
    have ht:=And.intro h.2.2.2.1 (And.intro h.2.2.2.2.1 (And.intro h.2.2.2.2.2.1 h.2.2.2.2.2.2))
    simpa only [RHHighDirichletBinning.field,RHHighDirichletBinning.bin,Nat.mul_zero,Nat.mul_one,
      Nat.pow_zero,Nat.div_one,hp480,pow_mul] using ht
  · have hc':c<96:=by omega
    have h:=TaoFivePrimes.rh_batch01_height_dirichlet_arithmetic29 c hc' j hj
    have he':44545+16*c+j=n:=by omega
    rw [he'] at h
    simp only [RHBatch01AllDirichletWords.packets,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some] at hw
    change (RHBatch01DirichletArithmetic.compute n).gammaRe=RHHighDirichletBinning.field (RHBatch01AllDirichletWords.word n) 0 ∧
      (RHBatch01DirichletArithmetic.compute n).gammaIm=RHHighDirichletBinning.field (RHBatch01AllDirichletWords.word n) 1 ∧
      RHBatch01DirichletArithmetic.delta n=RHHighDirichletBinning.field (RHBatch01AllDirichletWords.word n) 2 ∧
      RHBatch01DirichletArithmetic.bin n=RHHighDirichletBinning.bin (RHBatch01AllDirichletWords.word n)
    rw [hw]
    have ht:=And.intro h.2.2.2.1 (And.intro h.2.2.2.2.1 (And.intro h.2.2.2.2.2.1 h.2.2.2.2.2.2))
    simpa only [RHHighDirichletBinning.field,RHHighDirichletBinning.bin,Nat.mul_zero,Nat.mul_one,
      Nat.pow_zero,Nat.div_one,hp480,pow_mul] using ht
  · have hc':c<96:=by omega
    have h:=TaoFivePrimes.rh_batch01_height_dirichlet_arithmetic30 c hc' j hj
    have he':46081+16*c+j=n:=by omega
    rw [he'] at h
    simp only [RHBatch01AllDirichletWords.packets,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some] at hw
    change (RHBatch01DirichletArithmetic.compute n).gammaRe=RHHighDirichletBinning.field (RHBatch01AllDirichletWords.word n) 0 ∧
      (RHBatch01DirichletArithmetic.compute n).gammaIm=RHHighDirichletBinning.field (RHBatch01AllDirichletWords.word n) 1 ∧
      RHBatch01DirichletArithmetic.delta n=RHHighDirichletBinning.field (RHBatch01AllDirichletWords.word n) 2 ∧
      RHBatch01DirichletArithmetic.bin n=RHHighDirichletBinning.bin (RHBatch01AllDirichletWords.word n)
    rw [hw]
    have ht:=And.intro h.2.2.2.1 (And.intro h.2.2.2.2.1 (And.intro h.2.2.2.2.2.1 h.2.2.2.2.2.2))
    simpa only [RHHighDirichletBinning.field,RHHighDirichletBinning.bin,Nat.mul_zero,Nat.mul_one,
      Nat.pow_zero,Nat.div_one,hp480,pow_mul] using ht
  · have hc':c<96:=by omega
    have h:=TaoFivePrimes.rh_batch01_height_dirichlet_arithmetic31 c hc' j hj
    have he':47617+16*c+j=n:=by omega
    rw [he'] at h
    simp only [RHBatch01AllDirichletWords.packets,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some] at hw
    change (RHBatch01DirichletArithmetic.compute n).gammaRe=RHHighDirichletBinning.field (RHBatch01AllDirichletWords.word n) 0 ∧
      (RHBatch01DirichletArithmetic.compute n).gammaIm=RHHighDirichletBinning.field (RHBatch01AllDirichletWords.word n) 1 ∧
      RHBatch01DirichletArithmetic.delta n=RHHighDirichletBinning.field (RHBatch01AllDirichletWords.word n) 2 ∧
      RHBatch01DirichletArithmetic.bin n=RHHighDirichletBinning.bin (RHBatch01AllDirichletWords.word n)
    rw [hw]
    have ht:=And.intro h.2.2.2.1 (And.intro h.2.2.2.2.1 (And.intro h.2.2.2.2.2.1 h.2.2.2.2.2.2))
    simpa only [RHHighDirichletBinning.field,RHHighDirichletBinning.bin,Nat.mul_zero,Nat.mul_one,
      Nat.pow_zero,Nat.div_one,hp480,pow_mul] using ht
  · have hc':c<53:=by omega
    have h:=TaoFivePrimes.rh_batch01_height_dirichlet_arithmetic32 c hc' j hj
    have he':49153+16*c+j=n:=by omega
    rw [he'] at h
    simp only [RHBatch01AllDirichletWords.packets,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some] at hw
    change (RHBatch01DirichletArithmetic.compute n).gammaRe=RHHighDirichletBinning.field (RHBatch01AllDirichletWords.word n) 0 ∧
      (RHBatch01DirichletArithmetic.compute n).gammaIm=RHHighDirichletBinning.field (RHBatch01AllDirichletWords.word n) 1 ∧
      RHBatch01DirichletArithmetic.delta n=RHHighDirichletBinning.field (RHBatch01AllDirichletWords.word n) 2 ∧
      RHBatch01DirichletArithmetic.bin n=RHHighDirichletBinning.bin (RHBatch01AllDirichletWords.word n)
    rw [hw]
    have ht:=And.intro h.2.2.2.1 (And.intro h.2.2.2.2.1 (And.intro h.2.2.2.2.2.1 h.2.2.2.2.2.2))
    simpa only [RHHighDirichletBinning.field,RHHighDirichletBinning.bin,Nat.mul_zero,Nat.mul_one,
      Nat.pow_zero,Nat.div_one,hp480,pow_mul] using ht
#print axioms solution
