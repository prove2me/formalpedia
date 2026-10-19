-- Prove2me | solution 1 for TaoFivePrimes.rh_fast_window256_rescale_anchor
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T10:44:20.41882+00:00
-- url     : https://prove2.me/submissions/80b846f3-c4b2-4a42-93ea-5e065f075170

import Definitions.Def_TaoFivePrimes_RHFastWindow256Setup
import Definitions.Def_TaoFivePrimes_RHFastGaussianWindowFourier
import Definitions.Def_TaoFivePrimes_RHFastComplexBallInterface
import Theorems.Thm_TaoFivePrimes_rh_fast_complex_ball_soundness
import Theorems.Thm_TaoFivePrimes_rh_fast_window_center_seed
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
open Complex
namespace RHFastWindow256RescaleAnchorProof
open RHFastBallArithmetic RHFastBallSemantics
lemma rescale (a:Ball) (z:ℂ) (h:encloses RHFastBallSeedPrograms.D a z) :
 encloses RHFastWindow256Setup.D (RHFastWindow256Setup.lift a) z := by
 have hv:value RHFastWindow256Setup.D (RHFastWindow256Setup.lift a)=value RHFastBallSeedPrograms.D a := by
  unfold value RHFastWindow256Setup.lift RHFastWindow256Setup.D RHFastBallSeedPrograms.D
  push_cast
  norm_num
  ring
 have hr:((RHFastWindow256Setup.lift a).radius:ℝ)/(RHFastWindow256Setup.D:ℝ)=
  (a.radius:ℝ)/(RHFastBallSeedPrograms.D:ℝ) := by
  unfold RHFastWindow256Setup.lift RHFastWindow256Setup.D RHFastBallSeedPrograms.D
  push_cast
  norm_num
  ring
 simpa only [encloses,hv,hr] using h
lemma anchor_mem :
 encloses RHFastBallSeedPrograms.D
  (RHFastBallSeedPrograms.anchor 338465131998480615193183972069514375853 35120416548886332677381057571856482336 4235336350958928456860515144971299982 false)
  (RHFastGaussianWindow.anchor 3289999936) := by
 let D:=RHFastBallSeedPrograms.D
 let c:Int:=338465131998480615193183972069514375853
 let s:Int:=35120416548886332677381057571856482336
 let a:Int:=4235336350958928456860515144971299982
 let q:Ball:=⟨c,s,0⟩
 let b:Ball:=⟨a,0,0⟩
 let S:=TaoFivePrimes.rh_fast_complex_ball_soundness D (by norm_num [D,RHFastBallSeedPrograms.D])
 have h:=S.mul_mem b (power D q 8) (value D b) ((value D q)^8)
  (S.self_mem b) (S.power_mem q (value D q) 8 (S.self_mem q))
 have seed:=TaoFivePrimes.rh_fast_window_center_seed
 have hc:=congrArg (fun x=>x.1) seed
 have hs:=congrArg (fun x=>x.2.1) seed
 have ha:=congrArg (fun x=>x.2.2.1) seed
 have hn:=congrArg (fun x=>x.2.2.2) seed
 change (RHFastKernelGammaArithmetic.compute 3289999936 8192).cos=_ at hc
 change (RHFastKernelGammaArithmetic.compute 3289999936 8192).sin=_ at hs
 change (RHFastKernelGammaArithmetic.compute 3289999936 8192).amplitude=_ at ha
 change (RHFastKernelGammaArithmetic.compute 3289999936 8192).negative=_ at hn
 convert! h using 1
 unfold RHFastGaussianWindow.anchor
 dsimp only []
 rw [hc,hs,ha,hn]
 simp only [Bool.false_eq_true,ite_false]
 simp only [value,b,q,D,c,s,a,RHFastBallSeedPrograms.D,RHFastKernelLogData.D]
 norm_num
end RHFastWindow256RescaleAnchorProof

theorem solution :
 (∀(a:RHFastBallArithmetic.Ball)(z:ℂ),RHFastBallSemantics.encloses RHFastBallSeedPrograms.D a z →
  RHFastBallSemantics.encloses RHFastWindow256Setup.D (RHFastWindow256Setup.lift a) z) ∧
 RHFastBallSemantics.encloses RHFastBallSeedPrograms.D
  (RHFastBallSeedPrograms.anchor 338465131998480615193183972069514375853 35120416548886332677381057571856482336 4235336350958928456860515144971299982 false)
  (RHFastGaussianWindow.anchor 3289999936) :=
 ⟨RHFastWindow256RescaleAnchorProof.rescale,RHFastWindow256RescaleAnchorProof.anchor_mem⟩
#print axioms solution
