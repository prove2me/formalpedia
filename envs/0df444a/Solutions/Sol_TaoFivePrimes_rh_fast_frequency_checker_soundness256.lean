-- Prove2me | solution 1 for TaoFivePrimes.rh_fast_frequency_checker_soundness256
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T11:07:15.830829+00:00
-- url     : https://prove2.me/submissions/3a4c21e6-be67-4ad7-8fe0-b0fc45d647f7

import Definitions.Def_TaoFivePrimes_RHFastBallFrequencyChecker256
import Definitions.Def_TaoFivePrimes_RHFastGaussianWindowFourier
import Definitions.Def_TaoFivePrimes_RHFastComplexBallInterface
import Theorems.Thm_TaoFivePrimes_rh_fast_complex_ball_soundness
import Theorems.Thm_TaoFivePrimes_rh_fast_hermite_trace_soundness256
import Theorems.Thm_TaoFivePrimes_rh_fast_gaussian_trace_soundness256
import Theorems.Thm_TaoFivePrimes_rh_fast_ball_dot_product_soundness256
import Theorems.Thm_TaoFivePrimes_rh_fast_ball_budget_soundness256
import Mathlib.Data.List.Zip
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
open Complex Finset
namespace RHFastFrequency256SoundnessProof
open RHFastBallArithmetic RHFastBallSemantics RHFastBallFrequencyChecker256
lemma phase_period (d:Nat) : (-I)^(d%4)=(-I)^d := by
 symm
 calc
  (-I)^d=(-I)^(d%4+4*(d/4)) := by rw [Nat.mod_add_div]
  _ = _ := by rw [pow_add,pow_mul,show (-I)^4=1 by norm_num [pow_succ,pow_two],one_pow,mul_one]
lemma rotated_entry (qs:List Ball) (d:Nat) (hd:d<qs.length) :
 entry (rotated qs) d=rotate (entry qs d) d := by
 simp only [rotated,entry,List.getElem?_map,List.getElem?_zipIdx,
  List.getElem?_eq_getElem hd,Option.map_some,Option.getD_some,Nat.zero_add]
lemma drop_entry (hs:List Ball) (k d:Nat) : entry (hs.drop k) d=entry hs (d+k) := by
 simp only [entry,List.getElem?_drop,Nat.add_comm]
end RHFastFrequency256SoundnessProof

open RHFastBallArithmetic RHFastBallSemantics RHFastBallFrequencyChecker256 in
theorem solution (T j:Nat) (anchor pi root omega:Ball) (qs factors hs es ss:List Ball) (reference:List (Int×Int))
 (hA:encloses D anchor (RHFastGaussianWindow.anchor T))
 (hpi:encloses D pi (Real.pi:ℂ))
 (hroot:encloses D root ((Real.sqrt (2*Real.pi):ℝ):ℂ))
 (homega:encloses D omega ((RHFastGaussianWindow.omega T:ℝ):ℂ))
 (hqs:∀d:Nat,d<29→encloses D (entry qs d) ((RHFastGaussianWindow.proxyPolynomial T).coeff d))
 (hfactors:∀k:Nat,k<24→encloses D (entry factors k) (((-Real.pi:ℝ):ℂ)^k/(k.factorial:ℂ)))
 (hvalid:valid j anchor pi root omega qs factors hs es ss reference=true)
 (k:Nat) (hk:k<24) :
 ‖RHFastGaussianWindow.fourierFormula T k ((j:ℝ)/512)-
  (((((reference[k]?).getD (0,0)).1:ℂ)+((((reference[k]?).getD (0,0)).2:ℂ))*Complex.I)/(2:ℂ)^85)‖≤1/(2*10^15:ℝ) := by
 let S:=TaoFivePrimes.rh_fast_complex_ball_soundness D (by norm_num [D])
 let ν:ℝ:=RHFastGaussianWindow.frequency T ((j:ℝ)/512)
 have hv:=hvalid
 simp only [valid,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true,List.mem_range] at hv
 rcases hv with ⟨⟨⟨⟨⟨⟨hlen,hguard⟩,hbase⟩,hhermite⟩,hexp⟩,hsquare⟩,hbudget⟩
 rcases hlen with ⟨hql,hfl,hhl,hel,hsl,hrl⟩
 rcases hbase with ⟨hh0,hh1,he0,hs0⟩
 have hnu:encloses D (frequency pi omega j) (ν:ℂ) := by
  have h:=S.scale_mem _ _ 20 (S.sub_mem _ _ _ _
   (S.divide_mem _ _ 512 (by norm_num) (S.scale_mem pi (Real.pi:ℂ) ((2*j:Nat):Int) hpi)) homega)
  convert! h using 1
  simp only [ν,RHFastGaussianWindow.frequency]
  push_cast
  ring
 have hp:encloses D (pnu (frequency pi omega j)) (((5/64:ℝ)*ν:ℝ):ℂ) := by
  have h:=S.mul_mem _ _ _ _ hnu (S.rational_mem 5 64 (by norm_num))
  convert! h using 1
  push_cast
  norm_num
  ring
 have hx:encloses D (gaussianInput (frequency pi omega j)) (((-ν^2/2:ℝ):ℝ):ℂ) := by
  have h:=S.neg_mem _ _ (S.divide_mem _ _ 2 (by norm_num) (S.mul_mem _ _ _ _ hnu hnu))
  convert! h using 1
  push_cast
  norm_num
  ring
 have hh:=TaoFivePrimes.rh_fast_hermite_trace_soundness256 _ ν hp hs hh0 hh1 hhermite
 have he:=TaoFivePrimes.rh_fast_gaussian_trace_soundness256 _ (-ν^2/2) hx hguard.2 es ss he0 hexp hs0 hsquare
 have hc:encloses D (common anchor root (entry ss 20))
  (RHFastGaussianWindow.anchor T*20*((Real.sqrt (2*Real.pi)*Real.exp (-ν^2/2):ℝ):ℂ)) := by
  have h:=S.mul_mem _ _ _ _ (S.mul_mem _ _ _ _ hA (S.scale_mem _ _ 20 hroot)) he
  convert! h using 1
  push_cast
  norm_num
  ring
 have hrotlen:(rotated qs).length=29 := by simp only [rotated,List.length_map,List.length_zipIdx,hql]
 have hdot:encloses D (dot (rotated qs) (hs.drop k))
  (∑d∈Finset.range 29,(RHFastGaussianWindow.proxyPolynomial T).coeff d*(-I)^d*
   ((RHFastGaussianWindow.scaledHermite (d+k) ν:ℝ):ℂ)) := by
  have h:=TaoFivePrimes.rh_fast_ball_dot_product_soundness256 (rotated qs) (hs.drop k)
   (fun d=>(RHFastGaussianWindow.proxyPolynomial T).coeff d*(-I)^d)
   (fun d=>((RHFastGaussianWindow.scaledHermite (d+k) ν:ℝ):ℂ))
   (by rw [hrotlen,List.length_drop,hhl];omega) ?_ ?_
  · simpa only [hrotlen] using h
  · intro d hd
    have hd29:d<29:=by omega
    rw [RHFastFrequency256SoundnessProof.rotated_entry qs d (by omega)]
    have h:=S.rotate_mem _ _ d (hqs d hd29)
    convert! h using 1
    rw [RHFastFrequency256SoundnessProof.phase_period]
    ring
  · intro d hd
    rw [RHFastFrequency256SoundnessProof.drop_entry]
    exact hh (d+k) (by omega)
 have hout:encloses D (output (common anchor root (entry ss 20)) qs factors hs k)
  (RHFastGaussianWindow.fourierFormula T k ((j:ℝ)/512)) := by
  have h:=S.mul_mem _ _ _ _ (S.mul_mem _ _ _ _ hc (hfactors k hk)) hdot
  convert! h using 1
  try unfold RHFastGaussianWindow.fourierFormula
  <;> rfl
 exact TaoFivePrimes.rh_fast_ball_budget_soundness256 _ _ _ hout (hbudget k hk)
#print axioms solution
