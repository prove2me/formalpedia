-- Prove2me | solution 1 for TaoFivePrimes.rh_high_height_gamma_time_alias_bound
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-14T20:58:58.567589+00:00
-- url     : https://prove2.me/submissions/d5cc5850-dcf1-4691-9da4-d011945e03c7

import Mathlib
import Theorems.Thm_TaoFivePrimes_rh_high_height_scaled_gamma_bound
open Complex

namespace RHHighGammaFourier
noncomputable def window (T h t : ℝ) : ℂ :=
  Complex.exp ((Real.pi*(t+T)/4-t^2/(2*h^2):ℝ):ℂ)
noncomputable def gammaWindow (T h t : ℝ) : ℂ :=
  Complex.Gamma (1/4+(((t+T)/2:ℝ):ℂ)*I)*window T h t
end RHHighGammaFourier

namespace RHHighGammaTaylorFourier
open RHHighGammaFourier
noncomputable def moment (T : ℝ) (k : Nat) (t : ℝ) : ℂ :=
  gammaWindow T 20 t*(-2*(Real.pi:ℂ)*I*(t:ℂ))^k
end RHHighGammaTaylorFourier

set_option autoImplicit false
set_option maxHeartbeats 0
open Complex MeasureTheory Set
open scoped FourierTransform Topology
namespace RHHighGammaTimeTail
open RHHighGammaFourier RHHighGammaTaylorFourier
noncomputable def scaledMoment (T : ℝ) (k : Nat) (t : ℝ) : ℂ :=
  moment T k t/((k.factorial:ℂ)*(512:ℂ)^k)
lemma scaled_moment_norm (T t : ℝ) (k : Nat) :
    ‖scaledMoment T k t‖≤6*Real.exp (|t|/64-t^2/800) := by
  have hd : (0:ℝ)<(k.factorial:ℝ)*(512:ℝ)^k := by positivity
  have hg := TaoFivePrimes.rh_high_height_scaled_gamma_bound.2 T t 20 k
  norm_num only [show (2*(20:ℝ)^2)=800 by norm_num] at hg
  have hbase : ‖moment T k t‖≤6*(2*Real.pi*|t|)^k*Real.exp (-t^2/800) := by
    simpa only [moment,gammaWindow,window,Complex.ofReal_exp,
      show (2*(20:ℝ)^2)=800 by norm_num] using hg
  rw [scaledMoment,norm_div,norm_mul,norm_natCast,norm_pow,norm_ofNat]
  apply (div_le_div_of_nonneg_right hbase hd.le).trans
  have he : (6*(2*Real.pi*|t|)^k*Real.exp (-t^2/800))/((k.factorial:ℝ)*512^k)=
      6*((Real.pi*|t|/256)^k/(k.factorial:ℝ))*Real.exp (-t^2/800) := by
    rw [div_pow]
    field_simp
    rw [show (512:ℝ)^k=(2:ℝ)^k*256^k by rw [←mul_pow];norm_num]
    ring
  rw [he]
  have hp := Real.pow_div_factorial_le_exp (Real.pi*|t|/256) (by positivity) k
  have hu : Real.pi*|t|/256≤|t|/64 := by nlinarith [mul_nonneg (abs_nonneg t) (sub_nonneg.mpr Real.pi_lt_four.le)]
  calc
    _ ≤ 6*Real.exp (Real.pi*|t|/256)*Real.exp (-t^2/800) := by gcongr
    _ ≤ 6*Real.exp (|t|/64)*Real.exp (-t^2/800) := by gcongr
    _ = _ := by rw [mul_assoc,←Real.exp_add];congr 2;ring
lemma scaled_moment_tail (T t : ℝ) (k : Nat) (ht : 256≤|t|) :
    ‖scaledMoment T k t‖≤6*Real.exp (-|t|/4) := by
  apply (scaled_moment_norm T t k).trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Real.exp_le_exp.mpr
  nlinarith [sq_abs t,mul_nonneg (abs_nonneg t) (sub_nonneg.mpr ht)]
lemma positive_alias_term (T t : ℝ) (k n : Nat) (ht : -256≤t) :
    ‖scaledMoment T k (t+(n+1:ℝ)*512)‖≤6*Real.exp (-64*(n+1:ℝ)) := by
  have hn : (0:ℝ)≤n := by positivity
  have ha : 256≤t+(n+1:ℝ)*512 := by linarith
  have habs : |t+(n+1:ℝ)*512|=t+(n+1:ℝ)*512 := abs_of_nonneg (by linarith)
  apply (scaled_moment_tail T _ k (by rw [habs];exact ha)).trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Real.exp_le_exp.mpr
  rw [habs]
  linarith
lemma negative_alias_term (T t : ℝ) (k n : Nat) (ht : t≤256) :
    ‖scaledMoment T k (t-(n+1:ℝ)*512)‖≤6*Real.exp (-64*(n+1:ℝ)) := by
  have hn : (0:ℝ)≤n := by positivity
  have ha : t-(n+1:ℝ)*512≤ -256 := by linarith
  have habs : |t-(n+1:ℝ)*512|= -(t-(n+1:ℝ)*512) := abs_of_nonpos (by linarith)
  apply (scaled_moment_tail T _ k (by rw [habs];linarith)).trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Real.exp_le_exp.mpr
  rw [habs]
  linarith
end RHHighGammaTimeTail

set_option autoImplicit false
set_option maxHeartbeats 0
open Complex MeasureTheory Set
namespace RHHighGammaTimeTail
lemma geometric_error_hasSum : HasSum (fun n : Nat => 6*Real.exp (-64*(n+1:ℝ)))
    (6*Real.exp (-64)/(1-Real.exp (-64))) := by
  have hq0 : 0≤Real.exp (-64) := (Real.exp_pos _).le
  have hq1 : Real.exp (-64)<1 := Real.exp_lt_one_iff.mpr (by norm_num)
  have h := (hasSum_geometric_of_lt_one hq0 hq1).mul_left (6*Real.exp (-64))
  have hefun : (fun n : Nat => 6*Real.exp (-64*(n+1:ℝ)))=
      (fun n : Nat => (6*Real.exp (-64))*Real.exp (-64)^n) := by
    ext n
    have he : -64*(n+1:ℝ)=(-64:ℝ)+(n:ℝ)*(-64) := by ring
    rw [he,Real.exp_add,Real.exp_nat_mul]
    ring
  rw [hefun,show 6*Real.exp (-64)/(1-Real.exp (-64))=
    6*Real.exp (-64)*(1-Real.exp (-64))⁻¹ by ring]
  exact h
lemma geometric_error_small : 12*Real.exp (-64)/(1-Real.exp (-64))≤1/10^18 := by
  have hq1 : Real.exp (-64)<1 := Real.exp_lt_one_iff.mpr (by norm_num)
  have hp : (2:ℝ)^64≤Real.exp 64 := by
    have he : Real.exp (64:ℝ)=(Real.exp 1)^64 := by simpa using Real.exp_nat_mul (1:ℝ) (64:Nat)
    rw [he]
    exact pow_le_pow_left₀ (by norm_num) (by linarith [Real.exp_one_gt_two]) _
  have he : Real.exp (-64)*Real.exp 64=1 := by rw [←Real.exp_add];norm_num
  have hm := mul_le_mul_of_nonneg_left hp (Real.exp_pos (-64)).le
  rw [he] at hm
  have hq : Real.exp (-64)≤1/(2:ℝ)^64 := (le_div_iff₀ (by positivity)).mpr (by simpa [mul_comm] using hm)
  calc
    _ ≤ 12/((2:ℝ)^64-1) := by
      apply (div_le_div_iff₀ (by linarith) (by norm_num : (0:ℝ)<2^64-1)).mpr
      norm_num at hq ⊢
      nlinarith
    _ ≤ _ := by norm_num
lemma time_alias_mass (T t : ℝ) (k : Nat) (ht : -256≤t ∧ t≤256) :
    (∑' n : Nat, ‖scaledMoment T k (t+(n+1:ℝ)*512)‖)+
      (∑' n : Nat, ‖scaledMoment T k (t-(n+1:ℝ)*512)‖)≤1/10^18 := by
  have hg := geometric_error_hasSum.summable
  have hp := hg.of_nonneg_of_le (fun n => norm_nonneg _)
    (fun n => positive_alias_term T t k n ht.1)
  have hn := hg.of_nonneg_of_le (fun n => norm_nonneg _)
    (fun n => negative_alias_term T t k n ht.2)
  have hpb := hp.tsum_le_tsum (fun n => positive_alias_term T t k n ht.1) hg
  have hnb := hn.tsum_le_tsum (fun n => negative_alias_term T t k n ht.2) hg
  rw [geometric_error_hasSum.tsum_eq] at hpb hnb
  calc
    _ ≤ (6*Real.exp (-64)/(1-Real.exp (-64)))+
        (6*Real.exp (-64)/(1-Real.exp (-64))) := add_le_add hpb hnb
    _ = 12*Real.exp (-64)/(1-Real.exp (-64)) := by ring
    _ ≤ _ := geometric_error_small
end RHHighGammaTimeTail

 theorem solution :
  ∀ (T t : ℝ) (k : Nat), -256≤t → t≤256 →
  let φ : ℝ→ℂ := fun u => (Complex.Gamma (1/4+(((u+T)/2:ℝ):ℂ)*Complex.I)*
    Complex.exp ((Real.pi*(u+T)/4-u^2/(2*(20:ℝ)^2):ℝ):ℂ)*
      (-2*(Real.pi:ℂ)*Complex.I*(u:ℂ))^k)/((k.factorial:ℂ)*(512:ℂ)^k)
  (∑' n : Nat, ‖φ (t+(n+1:ℝ)*512)‖)+(∑' n : Nat, ‖φ (t-(n+1:ℝ)*512)‖)≤1/10^18 := by
  intro T t k ht ht'
  exact RHHighGammaTimeTail.time_alias_mass T t k ⟨ht,ht'⟩
