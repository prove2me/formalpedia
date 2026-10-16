-- Prove2me | solution 1 for TaoFivePrimes.rh_fast_log_horner_ball_soundness
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T10:08:16.513397+00:00
-- url     : https://prove2.me/submissions/94253357-2050-4ba4-a45e-6183830b127f

import Definitions.Def_TaoFivePrimes_RHFastBallSeedPrograms
import Definitions.Def_TaoFivePrimes_RHFastComplexBallInterface
import Theorems.Thm_TaoFivePrimes_rh_fast_complex_ball_soundness
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
open Complex Finset
namespace RHFastLogHornerSoundness
open RHFastBallArithmetic RHFastBallSemantics
noncomputable def series (m n:Nat) (z:ℂ) : ℂ :=
 ∑j∈Finset.range n,z^j/((2*(m+j)+1:Nat):ℂ)
lemma series_succ (m n:Nat) (z:ℂ) :
 series m (n+1) z=1/((2*m+1:Nat):ℂ)+z*series (m+1) n z := by
 unfold series
 rw [Finset.sum_range_succ']
 simp only [pow_zero,Nat.add_zero]
 rw [add_comm]
 congr 1
 rw [Finset.mul_sum]
 apply Finset.sum_congr rfl
 intro j hj
 have he:2*(m+(j+1))+1=2*((m+1)+j)+1:=by omega
 rw [he,pow_succ]
 ring
lemma sound (D:Nat) (hD:0<D) (x:Ball) (z:ℂ) (hx:encloses D x z) (m n:Nat) :
 encloses D (RHFastBallSeedPrograms.horner D x m n) (series m n z) := by
 let S:=TaoFivePrimes.rh_fast_complex_ball_soundness D hD
 induction n using Nat.twoStepInduction generalizing m with
 | zero=>
  have hz:encloses D zero (0:ℂ):=by simpa [integer,zero] using S.integer_mem 0
  simpa only [RHFastBallSeedPrograms.horner,series,Finset.range_zero,Finset.sum_empty] using hz
 | one=>
  have h:=S.rational_mem 1 (2*m+1) (by omega)
  simpa only [RHFastBallSeedPrograms.horner,series,Finset.sum_range_one,pow_zero,
   Nat.add_zero,Int.cast_one] using h
 | more n hn hn1=>
  change encloses D (add (rational D 1 (2*m+1))
   (mul D x (RHFastBallSeedPrograms.horner D x (m+1) (n+1)))) (series m (n+2) z)
  rw [series_succ]
  apply S.add_mem
  · simpa only [Int.cast_one] using S.rational_mem 1 (2*m+1) (by omega)
  · exact S.mul_mem _ _ _ _ hx (hn1 (m+1))
end RHFastLogHornerSoundness

theorem solution (D:Nat) (hD:0<D) (x:RHFastBallArithmetic.Ball) (z:ℂ)
 (hx:RHFastBallSemantics.encloses D x z) (m n:Nat) :
 RHFastBallSemantics.encloses D (RHFastBallSeedPrograms.horner D x m n)
   (∑j∈Finset.range n,z^j/((2*(m+j)+1:Nat):ℂ)) :=
 RHFastLogHornerSoundness.sound D hD x z hx m n
#print axioms solution
