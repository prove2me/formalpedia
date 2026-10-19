-- Prove2me | solution 1 for TaoFivePrimes.rh_fast_gaussian_trace_soundness256
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T10:52:58.249719+00:00
-- url     : https://prove2.me/submissions/a9cd9e0e-fe7c-407f-9e26-94df766fa0f2

import Definitions.Def_TaoFivePrimes_RHFastBallFrequencyChecker256
import Definitions.Def_TaoFivePrimes_RHFastComplexBallInterface
import Theorems.Thm_TaoFivePrimes_rh_fast_complex_ball_soundness
import Theorems.Thm_TaoFivePrimes_rh_fast_exponential_trace_soundness256
import Theorems.Thm_TaoFivePrimes_rh_fast_complex_exp_remainder256
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
open Complex
namespace RHFastGaussianTrace256Proof
open RHFastBallArithmetic RHFastBallSemantics RHFastBallFrequencyChecker256
lemma value_norm (D:Nat) (hD:0<D) (a:Ball) :
 ‖value D a‖≤(magnitude a:ℝ)/(D:ℝ) := by
 rw [value,norm_div,Complex.norm_natCast]
 apply div_le_div_of_nonneg_right _ (by positivity)
 calc
  _ ≤ ‖(a.re:ℂ)‖+‖(a.im:ℂ)*I‖:=norm_add_le _ _
  _ = (magnitude a:ℝ):=by
   rw [norm_mul,norm_I,mul_one,←norm_natAbs a.re,←norm_natAbs a.im]
   simp only [Complex.norm_natCast,magnitude,Nat.cast_add]
lemma perturb (D:Nat) (a:Ball) (x y:ℂ) (n:Nat)
 (hx:encloses D a x) (hy:‖y-x‖≤(n:ℝ)/(D:ℝ)) : encloses D (inflate a n) y := by
 unfold encloses at hx ⊢
 have h:=norm_sub_le_norm_sub_add_norm_sub y x (value D a)
 apply h.trans
 convert! add_le_add hy hx using 1 <;> simp only [inflate,Nat.cast_add] <;> ring

lemma norm_bound (a:Ball) (z:ℂ) (hz:encloses D a z) (h: magnitude a+a.radius≤65536*D) : ‖z‖≤65536 := by
 have hD:0<D:=by norm_num [D]
 have hDr:(0:ℝ)<D:=by exact_mod_cast hD
 have hb:=value_norm D hD a
 have ht:=norm_le_norm_sub_add z (value D a)
 unfold encloses at hz
 have hm:((magnitude a:ℝ)+(a.radius:ℝ))/(D:ℝ)≤65536 := by
  apply (div_le_iff₀ hDr).mpr
  exact_mod_cast h
 have he:(a.radius:ℝ)/(D:ℝ)+(magnitude a:ℝ)/(D:ℝ)=((magnitude a:ℝ)+(a.radius:ℝ))/(D:ℝ):=by ring
 exact (ht.trans (add_le_add hz hb)).trans (he.le.trans hm)
lemma checked (a:Ball) (x:ℝ) (hx:encloses D a (x:ℂ))
 (hb:magnitude a+a.radius≤65536*D) (es ss:List Ball)
 (he0:entry es 0=integer D 1)
 (hestep:∀n:Nat,n<40→entry es (n+1)=expStep (divide a (2^20)) n (entry es n))
 (hs0:entry ss 0=inflate (entry es 40) 1)
 (hsstep:∀n:Nat,n<20→entry ss (n+1)=mul D (entry ss n) (entry ss n)) :
 encloses D (entry ss 20) ((Real.exp x:ℝ):ℂ) := by
 let S:=TaoFivePrimes.rh_fast_complex_ball_soundness D (by norm_num [D])
 let z:ℂ:=(x:ℂ)/(2:ℂ)^20
 have hz:encloses D (divide a (2^20)) z := by
  convert! S.divide_mem a (x:ℂ) 1048576 (by decide) hx using 1 <;> norm_num [z]
 have hn:‖z‖≤1/16 := by
  have h:=norm_bound a (x:ℂ) hx hb
  dsimp only [z]
  rw [norm_div,Complex.norm_pow,Complex.norm_ofNat]
  apply (div_le_iff₀ (by norm_num : (0:ℝ)<2^20)).mpr
  norm_num
  simpa only [Complex.norm_real,Real.norm_eq_abs] using h
 have he:=TaoFivePrimes.rh_fast_exponential_trace_soundness256 (divide a (2^20)) z hz es he0 hestep
 have hr:=TaoFivePrimes.rh_fast_complex_exp_remainder256 z hn
 have hex:encloses D (entry ss 0) (Complex.exp z) := by
  rw [hs0]
  apply perturb D _ _ _ 1 he
  simpa only [D,Nat.cast_pow,Nat.cast_ofNat,Nat.cast_one] using hr
 have hs (n:Nat) (hn:n≤20) : encloses D (entry ss n) (Complex.exp ((2:ℂ)^n*z)) := by
  induction n with
  | zero=>simpa only [pow_zero,one_mul] using hex
  | succ n ih=>
   rw [hsstep n (by omega)]
   have hi:=ih (by omega)
   have h:=S.mul_mem _ _ _ _ hi hi
   convert! h using 1
   rw [←Complex.exp_add]
   congr 1
   rw [pow_succ]
   ring
 have hf:=hs 20 (by omega)
 convert! hf using 1
 simp only [z,Complex.ofReal_exp]
 congr 1
 norm_num
 <;> ring
end RHFastGaussianTrace256Proof

theorem solution (a:RHFastBallArithmetic.Ball) (x:ℝ)
 (hx:RHFastBallSemantics.encloses RHFastBallFrequencyChecker256.D a (x:ℂ))
 (hb:RHFastBallArithmetic.magnitude a+a.radius≤65536*RHFastBallFrequencyChecker256.D)
 (es ss:List RHFastBallArithmetic.Ball)
 (he0:RHFastBallFrequencyChecker256.entry es 0=RHFastBallArithmetic.integer RHFastBallFrequencyChecker256.D 1)
 (hestep:∀n:Nat,n<40→RHFastBallFrequencyChecker256.entry es (n+1)=RHFastBallFrequencyChecker256.expStep
  (RHFastBallArithmetic.divide a (2^20)) n (RHFastBallFrequencyChecker256.entry es n))
 (hs0:RHFastBallFrequencyChecker256.entry ss 0=RHFastBallArithmetic.inflate (RHFastBallFrequencyChecker256.entry es 40) 1)
 (hsstep:∀n:Nat,n<20→RHFastBallFrequencyChecker256.entry ss (n+1)=RHFastBallArithmetic.mul RHFastBallFrequencyChecker256.D
  (RHFastBallFrequencyChecker256.entry ss n) (RHFastBallFrequencyChecker256.entry ss n)) :
 RHFastBallSemantics.encloses RHFastBallFrequencyChecker256.D (RHFastBallFrequencyChecker256.entry ss 20)
  ((Real.exp x:ℝ):ℂ) := RHFastGaussianTrace256Proof.checked a x hx hb es ss he0 hestep hs0 hsstep
#print axioms solution
