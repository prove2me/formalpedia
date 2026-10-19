-- Prove2me | solution 1 for TaoFivePrimes.rh_fresh16_anchor_soundness
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T13:12:26.950102+00:00
-- url     : https://prove2.me/submissions/3105521a-9bea-44fe-82a1-08a679d891ba

import Definitions.Def_TaoFivePrimes_RHFastWindow256Setup
import Definitions.Def_TaoFivePrimes_RHFastGaussianWindowFourier
import Definitions.Def_TaoFivePrimes_RHFastComplexBallInterface
import Theorems.Thm_TaoFivePrimes_rh_fast_complex_ball_soundness
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option maxRecDepth 1000000
open Complex
namespace RHFreshAnchorSoundnessProof
open RHFastBallArithmetic RHFastBallSemantics
lemma anchor_mem (T:Nat) :
 encloses RHFastBallSeedPrograms.D
  (RHFastBallSeedPrograms.anchor (RHFastKernelGammaArithmetic.compute T 8192).cos
   (RHFastKernelGammaArithmetic.compute T 8192).sin
   (RHFastKernelGammaArithmetic.compute T 8192).amplitude
   (RHFastKernelGammaArithmetic.compute T 8192).negative)
  (RHFastGaussianWindow.anchor T) := by
 let D:=RHFastBallSeedPrograms.D
 let c: Int:=(RHFastKernelGammaArithmetic.compute T 8192).cos
 let s: Int:=(RHFastKernelGammaArithmetic.compute T 8192).sin
 let a: Int:=(RHFastKernelGammaArithmetic.compute T 8192).amplitude
 let negative:Bool:=(RHFastKernelGammaArithmetic.compute T 8192).negative
 let q:Ball:=⟨c,(if negative then -s else s),0⟩
 let b:Ball:=⟨a,0,0⟩
 let S:=TaoFivePrimes.rh_fast_complex_ball_soundness D (by norm_num [D,RHFastBallSeedPrograms.D])
 have h:=S.mul_mem b (power D q 8) (value D b) ((value D q)^8)
  (S.self_mem b) (S.power_mem q (value D q) 8 (S.self_mem q))
 convert! h using 1
 unfold RHFastGaussianWindow.anchor
 dsimp only []
 cases hn:(RHFastKernelGammaArithmetic.compute T 8192).negative <;>
  simp [value,b,q,D,c,s,a,negative,RHFastBallSeedPrograms.D,RHFastKernelLogData.D,hn,map_div,map_add,map_mul,map_natCast,map_intCast,map_ofNat,Complex.conj_I] <;> norm_num <;> ring
end RHFreshAnchorSoundnessProof

theorem solution (T:Nat) :
 RHFastBallSemantics.encloses RHFastBallSeedPrograms.D
  (RHFastBallSeedPrograms.anchor (RHFastKernelGammaArithmetic.compute T 8192).cos
   (RHFastKernelGammaArithmetic.compute T 8192).sin
   (RHFastKernelGammaArithmetic.compute T 8192).amplitude
   (RHFastKernelGammaArithmetic.compute T 8192).negative)
  (RHFastGaussianWindow.anchor T) := RHFreshAnchorSoundnessProof.anchor_mem T
#print axioms solution
