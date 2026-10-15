-- Prove2me | solution 1 for ThreeSum1960614.fixed_model_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-14T13:37:46.328433+00:00
-- url     : https://prove2.me/submissions/11fed256-8412-4818-9772-e4a1cf7558bc

import Definitions.Def_ThreeSum1960614_Analysis
import Definitions.Def_ThreeSum1960614_FixedModelAlgebra
import Definitions.Def_ThreeSum1960614_ModelWitnessPoints
import Theorems.Thm_ThreeSum1960614_FixedModel_bound_of_witnesses
import Theorems.Thm_ThreeSum1960614_FixedModel_witness_logs
import Theorems.Thm_ThreeSum1960614_encoding_parameter_bounds
import Theorems.Thm_ThreeSum1960614_high_precision_logs

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 10000

noncomputable section
namespace ThreeSum1960614.FixedModel

private theorem entropy_eq (t : ℝ) :
    entropy t = (-t*Real.log t-(1-t)*Real.log (1-t))/Real.log 2 := by
  simp only [entropy,Real.binEntropy,Real.log_inv]
  ring

private theorem log_232 : Real.log (232 : ℝ) = 7*Real.log 2+Real.log (29/16) := by
  have hp := Real.log_pow (2 : ℝ) 7
  norm_num at hp
  rw [show (232 : ℝ)=128*(29/16) by norm_num,
    Real.log_mul (by norm_num : (128 : ℝ) ≠ 0) (by norm_num : (29/16 : ℝ) ≠ 0),hp]

private theorem log_231 :
    Real.log (231 : ℝ)=7*Real.log 2+Real.log (29/16)-Real.log (232/231) := by
  rw [Real.log_div (by norm_num : (232 : ℝ) ≠ 0) (by norm_num : (231 : ℝ) ≠ 0),log_232]
  ring

private theorem scaled_entropy (x : ℝ) (hx : 0 < x) (hx1 : x < 232) :
    232*entropy (x/232)=
      (232*Real.log 232-x*Real.log x-(232-x)*Real.log (232-x))/Real.log 2 := by
  have hn : 232-x ≠ 0 := by linarith
  rw [entropy_eq,show 1-x/232=(232-x)/232 by ring,
    Real.log_div hx.ne' (by norm_num : (232 : ℝ) ≠ 0),
    Real.log_div hn (by norm_num : (232 : ℝ) ≠ 0)]
  ring

private theorem log_one_sub (t : ℝ) (ht : t < 1) :
    Real.log (1-t)=Real.log (2*(1-t))-Real.log 2 := by
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by linarith : 1-t ≠ 0)]
  ring

private theorem log_231_add (t : ℝ) (ht : 0 ≤ t) :
    Real.log (231+t)=Real.log 231+Real.log (1+t/231) := by
  rw [show (231+t : ℝ)=231*(1+t/231) by ring,
    Real.log_mul (by norm_num : (231 : ℝ) ≠ 0) (by positivity : 1+t/231 ≠ 0)]

theorem gamma_formula (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1/2) :
    gamma 232 t =
      ((8*t-1)*Real.log 2+(1-t)*Real.log (2*(1-t))+
        t*(Real.log (29/16)-Real.log (232/231))+
        (231+t)*Real.log (1+t/231))/Real.log 2 := by
  have ht : t < 1 := by linarith
  unfold gamma
  norm_num only [Nat.cast_ofNat]
  rw [scaled_entropy 1 (by norm_num) (by norm_num),
    scaled_entropy (1-t) (by linarith) (by linarith)]
  simp only [show (232 : ℝ)-1=231 by norm_num]
  rw [Real.log_one,show 232-(1-t)=(231+t : ℝ) by ring,
    log_one_sub t ht,log_231_add t ht0]
  simp only [log_231,log_232]
  ring

theorem entropy_scaled_formula (k : ℕ) (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) :
    entropy t =
      ((1+((k : ℝ)-1)*t)*Real.log 2-t*Real.log (2^k*t)-
        (1-t)*Real.log (2*(1-t)))/Real.log 2 := by
  have hl : Real.log t=Real.log (2^k*t)-(k : ℝ)*Real.log 2 := by
    rw [Real.log_mul (by positivity : (2 : ℝ)^k ≠ 0) ht0.ne',Real.log_pow]
    ring
  rw [entropy_eq,hl,log_one_sub t ht1]
  ring

theorem entropy_monotone : MonotoneOn entropy (Set.Icc (0 : ℝ) (1/2)) := by
  intro x hx y hy hxy
  exact div_le_div_of_nonneg_right
    (Real.binEntropy_strictMonoOn.monotoneOn
      (by simpa only [one_div] using hx) (by simpa only [one_div] using hy) hxy)
    (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le

theorem gamma_monotone : MonotoneOn (gamma 232) (Set.Icc (0 : ℝ) (1/2)) := by
  intro x hx y hy hxy
  have harg : (1-y)/232 ≤ (1-x)/232 := by linarith
  have hl : (1-y)/232 ∈ Set.Icc (0 : ℝ) (1/2) := by constructor <;> linarith [hy.1,hy.2]
  have hu : (1-x)/232 ∈ Set.Icc (0 : ℝ) (1/2) := by constructor <;> linarith [hx.1,hx.2]
  have h := entropy_monotone hl hu harg
  unfold gamma
  norm_num only [Nat.cast_ofNat]
  linarith

theorem gamma_nonnegative {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) (1/2)) : 0 ≤ gamma 232 t := by
  have h := gamma_monotone (by norm_num : (0 : ℝ) ∈ Set.Icc 0 (1/2)) ht ht.1
  simpa only [gamma,sub_zero,zero_mul,one_mul,sub_self] using h

theorem split_gamma_bound : gamma 232 split ≤ gammaCap := by
  obtain ⟨hl2,hl29,hl231,_,_,_⟩ := ThreeSum1960614.high_precision_logs
  obtain ⟨_,hs,hg,_,_,_⟩ := witness_logs
  rw [gamma_formula split (by norm_num [split]) (by norm_num [split]),
    div_le_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))]
  norm_num [split,gammaCap] at hs hg ⊢
  nlinarith only [hl2.1,hl29.2,hl231.1,hs.2,hg.2]

theorem split_entropy_bound : entropyFloor ≤ entropy split := by
  obtain ⟨hl2,_,_,_,_,_⟩ := ThreeSum1960614.high_precision_logs
  obtain ⟨ht,hs,_,_,_,_⟩ := witness_logs
  rw [entropy_scaled_formula 5 split (by norm_num [split]) (by norm_num [split]),
    le_div_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))]
  norm_num [split,entropyFloor] at ht hs ⊢
  nlinarith only [hl2.1,ht.2,hs.2]

theorem ratio_point_bound : ratio0*(1+gamma 232 ratioPoint) < entropy ratioPoint := by
  obtain ⟨hl2,hl29,hl231,_,_,_⟩ := ThreeSum1960614.high_precision_logs
  obtain ⟨_,_,_,hu,hs,hg⟩ := witness_logs
  rw [gamma_formula ratioPoint (by norm_num [ratioPoint]) (by norm_num [ratioPoint]),
    entropy_scaled_formula 3 ratioPoint (by norm_num [ratioPoint]) (by norm_num [ratioPoint])]
  apply (lt_div_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mpr
  have hln : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  have hid (N : ℝ) : ratio0*(1+N/Real.log 2)*Real.log 2 = ratio0*(Real.log 2+N) := by
    field_simp [hln] <;> ring
  rw [hid]
  norm_num [ratio0,ratioPoint] at hu hs hg ⊢
  nlinarith only [hl2.1,hl29.2,hl231.1,hu.2,hs.2,hg.2]



end ThreeSum1960614.FixedModel

end

open ThreeSum1960614 ThreeSum1960614.FixedModel in
theorem solution (e b S th terminal ratio R : ℝ)
    (hmodel : ModelFeasible 232 e b S th terminal ratio R) : lowerTarget < R := by
  have hE : e0 ≤ E 232 := by
    simpa only [e0] using ThreeSum1960614.encoding_parameter_bounds.1.le
  have hk : k0 ≤ kappa 232 := by
    have h := ThreeSum1960614.encoding_parameter_bounds.2.2.1.le
    norm_num [k0] at h ⊢
    exact h
  have hm := hmodel
  rcases hm with ⟨_,_,_,_,hth0,hth1,_,_,_,_,huniform,_⟩
  have hp : ratioPoint ∈ Set.Icc (0 : ℝ) (1/2) := by norm_num [ratioPoint]
  have hrho : ratio0 ≤ ratio := by
    have h := huniform ratioPoint hp
    have hw := ratio_point_bound
    have hden : 0 < 1+gamma 232 ratioPoint := by linarith [gamma_nonnegative hp]
    by_contra hn
    have hm := mul_lt_mul_of_pos_right (lt_of_not_ge hn) hden
    exact (not_lt_of_ge h) (hm.trans hw)
  apply bound_of_witnesses e b S th terminal ratio R hmodel hE hk hrho
  · intro hle
    exact (gamma_monotone ⟨hth0,hth1⟩ (by norm_num [split]) hle).trans split_gamma_bound
  · intro hle
    exact split_entropy_bound.trans
      (entropy_monotone (by norm_num [split]) ⟨hth0,hth1⟩ hle)

#print axioms solution
