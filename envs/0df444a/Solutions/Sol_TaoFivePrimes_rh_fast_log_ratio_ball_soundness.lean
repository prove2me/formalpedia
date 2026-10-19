-- Prove2me | solution 1 for TaoFivePrimes.rh_fast_log_ratio_ball_soundness
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T10:32:19.872984+00:00
-- url     : https://prove2.me/submissions/c6f154ac-8c43-4934-9a52-c49f9dc86d98

import Definitions.Def_TaoFivePrimes_RHFastBallSeedPrograms
import Definitions.Def_TaoFivePrimes_RHFastComplexBallInterface
import Theorems.Thm_TaoFivePrimes_rh_fast_complex_ball_soundness
import Theorems.Thm_TaoFivePrimes_rh_fast_log_horner_ball_soundness
import Theorems.Thm_TaoFivePrimes_rh_fast_log_ratio_polynomial
set_option Elab.async false
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Complex Finset
namespace RHFastLogRatioSeedProof
open RHFastBallArithmetic RHFastBallSemantics
lemma perturb (D:Nat) (a:Ball) (x y:ℂ) (n:Nat)
 (hx:encloses D a x) (hy:‖y-x‖≤(n:ℝ)/(D:ℝ)) : encloses D (inflate a n) y := by
 unfold encloses at hx ⊢
 have h:=norm_sub_le_norm_sub_add_norm_sub y x (value D a)
 apply h.trans
 convert! add_le_add hy hx using 1 <;> simp only [inflate,Nat.cast_add] <;> ring
lemma sound (n d:Nat) (hd:0<d) (hlo:d ≤ n) (hhi:n ≤ 2*d) :
 encloses RHFastBallSeedPrograms.D (RHFastBallSeedPrograms.logRatio n d)
   ((Real.log ((n:ℝ)/(d:ℝ)):ℝ):ℂ) := by
 let D:=RHFastBallSeedPrograms.D
 have hD:0<D:=by norm_num [D,RHFastBallSeedPrograms.D]
 let S:=TaoFivePrimes.rh_fast_complex_ball_soundness D hD
 let x:ℝ:=((n:ℝ)-(d:ℝ))/((n:ℝ)+(d:ℝ))
 let a:Ball:=rational D ((n:Int)-(d:Int)) (n+d)
 let b:Ball:=mul D a a
 let u:Ball:=RHFastBallSeedPrograms.horner D b 0 64
 let v:Ball:=scale (mul D a u) 2
 have hdr:(0:ℝ)<d:=by exact_mod_cast hd
 have hlr:(d:ℝ)≤n:=by exact_mod_cast hlo
 have hhr:(n:ℝ)≤2*(d:ℝ):=by exact_mod_cast hhi
 have hden:0<(n:ℝ)+(d:ℝ):=by positivity
 have hx0:0≤x:=div_nonneg (by linarith) hden.le
 have hx1:x≤1/3:=by
  dsimp only [x]
  apply (div_le_iff₀ hden).mpr
  linarith
 have ha:encloses D a (x:ℂ) := by
  have h:=S.rational_mem ((n:Int)-(d:Int)) (n+d) (by omega)
  convert! h using 1
  dsimp only [x]
  push_cast
  rfl
 have hb:encloses D b ((x:ℂ)^2) := by
  simpa only [b,pow_two] using S.mul_mem a a (x:ℂ) (x:ℂ) ha ha
 have hu:=TaoFivePrimes.rh_fast_log_horner_ball_soundness D hD b ((x:ℂ)^2) hb 0 64
 have hu':encloses D u (∑j∈Finset.range 64,(x:ℂ)^(2*j)/((2*j+1:Nat):ℂ)) := by
  simpa only [u,Nat.zero_add,←pow_mul] using hu
 have hv:encloses D v
   (2*(x:ℂ)*(∑j∈Finset.range 64,(x:ℂ)^(2*j)/((2*j+1:Nat):ℂ))) := by
  have h:=S.scale_mem (mul D a u)
   ((x:ℂ)*(∑j∈Finset.range 64,(x:ℂ)^(2*j)/((2*j+1:Nat):ℂ))) 2
   (S.mul_mem _ _ _ _ ha hu')
  convert! h using 1 <;> (norm_num only <;> ring)
 have hy:(n:ℝ)/(d:ℝ)=(1+x)/(1-x) := by
  apply (div_eq_div_iff hdr.ne' (by linarith:1-x≠0)).mpr
  dsimp only [x]
  field_simp [hden.ne']
  ring
 have hp:=TaoFivePrimes.rh_fast_log_ratio_polynomial x hx0 hx1
 rw [←hy] at hp
 have hp':‖((Real.log ((n:ℝ)/(d:ℝ)):ℝ):ℂ)-
   2*(x:ℂ)*(∑j∈Finset.range 64,(x:ℂ)^(2*j)/((2*j+1:Nat):ℂ))‖≤1/(D:ℝ) := by
  simpa only [D,RHFastBallSeedPrograms.D,Nat.cast_pow,Nat.cast_ofNat] using hp
 have hfinal:=perturb D v _ ((Real.log ((n:ℝ)/(d:ℝ)):ℝ):ℂ) 1 hv (by simpa only [Nat.cast_one] using hp')
 simpa only [RHFastBallSeedPrograms.logRatio,D,a,b,u,v] using hfinal
end RHFastLogRatioSeedProof

theorem solution (n d:Nat) (hd:0<d) (hlo:d ≤ n) (hhi:n ≤ 2*d) :
 RHFastBallSemantics.encloses RHFastBallSeedPrograms.D (RHFastBallSeedPrograms.logRatio n d)
   ((Real.log ((n:ℝ)/(d:ℝ)):ℝ):ℂ) := RHFastLogRatioSeedProof.sound n d hd hlo hhi
#print axioms solution
