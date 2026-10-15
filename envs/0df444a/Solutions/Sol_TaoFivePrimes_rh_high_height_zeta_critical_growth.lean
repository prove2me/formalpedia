-- Prove2me | solution 1 for TaoFivePrimes.rh_high_height_zeta_critical_growth
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-14T21:06:58.175226+00:00
-- url     : https://prove2.me/submissions/97b4675b-f651-4f51-8389-7f29ee68b670

import Theorems.Thm_SWPort_Zeta0EqZeta
set_option autoImplicit false
set_option maxHeartbeats 0
open Complex MeasureTheory Set
namespace RHHighZetaGrowth
noncomputable def saw (x : ℝ) : ℂ := (((Int.floor x:ℝ)+1/2-x:ℝ):ℂ)
lemma saw_norm (x : ℝ) : ‖saw x‖≤1/2 := by
  rw [saw,Complex.norm_real,Real.norm_eq_abs]
  exact abs_le.mpr ⟨by linarith [Int.lt_floor_add_one x],by linarith [Int.floor_le x]⟩
lemma saw_integral_norm (s : ℂ) (hs : s.re=1/2) :
    ‖∫ x : ℝ in Ioi 1, saw x/(x:ℂ)^(s+1)‖≤1 := by
  have hi : IntegrableOn (fun x : ℝ => (1/2)*x^(-(3/2:ℝ))) (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num : -(3/2:ℝ)< -1) (by norm_num : (0:ℝ)<1)).const_mul _
  have hb : ∀ᵐ x : ℝ ∂volume.restrict (Ioi 1), ‖saw x/(x:ℂ)^(s+1)‖≤(1/2)*x^(-(3/2:ℝ)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : 0<x := by linarith [mem_Ioi.mp hx]
    rw [norm_div,Complex.norm_cpow_eq_rpow_re_of_pos hx0]
    simp only [add_re,one_re,hs]
    norm_num
    have he : (1/2:ℝ)/x^(3/2:ℝ)=(1/2)*x^(-(3/2:ℝ)) := by
      rw [Real.rpow_neg hx0.le]
      ring
    exact (div_le_div_of_nonneg_right (saw_norm x) (Real.rpow_pos_of_pos hx0 _).le).trans_eq he
  calc
    _ ≤ ∫ x : ℝ in Ioi 1, (1/2)*x^(-(3/2:ℝ)) := norm_integral_le_of_norm_le hi hb
    _ = 1 := by rw [integral_const_mul,integral_Ioi_rpow_of_lt (by norm_num) (by norm_num : (0:ℝ)<1)];norm_num
lemma critical_growth (t : ℝ) : ‖riemannZeta (1/2+(t:ℂ)*I)‖≤3+|t| := by
  let s : ℂ := 1/2+(t:ℂ)*I
  have hs : s.re=1/2 := by simp [s]
  have hs0 : s≠0 := by intro he;have hr:=congrArg Complex.re he;rw [hs] at hr;norm_num at hr
  have hs1 : s≠1 := by intro he;have hr:=congrArg Complex.re he;rw [hs] at hr;norm_num at hr
  have hz := SWPort.Zeta0EqZeta (N:=1) (by norm_num) (s:=s) (by rw [hs];norm_num) hs1
  have he : riemannZeta s=(1/2:ℂ)-1/(1-s)+s*(∫ x : ℝ in Ioi 1, saw x/(x:ℂ)^(s+1)) := by
    rw [←hz]
    unfold SWPort.riemannZeta0
    simp only [Finset.sum_range_succ,Finset.sum_range_zero,add_zero,zero_add,Nat.cast_zero,
      Nat.cast_one,Complex.zero_cpow hs0,Complex.one_cpow,div_zero,zero_div,div_one]
    have hf : (fun x : ℝ => ((⌊x⌋:ℂ)+1/2-(x:ℂ))/(x:ℂ)^(s+1))=
        (fun x : ℝ => saw x/(x:ℂ)^(s+1)) := by ext x;unfold saw;push_cast;rfl
    rw [hf]
    ring
  have hd : 1/2≤‖1-s‖ := by
    have hr := Complex.re_le_norm (1-s)
    simpa only [sub_re,one_re,hs,show (1-1/2:ℝ)=1/2 by norm_num] using hr
  have hrec : ‖1/(1-s)‖≤2 := by
    rw [norm_div,norm_one]
    apply (div_le_iff₀ (by linarith : 0<‖1-s‖)).mpr
    linarith
  have hsn : ‖s‖≤1/2+|t| := by
    have h := norm_add_le (1/2:ℂ) ((t:ℂ)*I)
    simpa only [s,norm_mul,Complex.norm_I,mul_one,Complex.norm_real,Real.norm_eq_abs,
      norm_div,norm_one,norm_ofNat,show |t|=|t| by rfl] using h
  change ‖riemannZeta s‖≤_
  rw [he]
  calc
    _ ≤ ‖(1/2:ℂ)-1/(1-s)‖+‖s*(∫ x : ℝ in Ioi 1, saw x/(x:ℂ)^(s+1))‖ := norm_add_le _ _
    _ ≤ (1/2+2)+‖s‖*1 := by
      apply add_le_add
      · exact (norm_sub_le _ _).trans (add_le_add (by norm_num) hrec)
      · rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (saw_integral_norm s hs) (norm_nonneg _)
    _ ≤ _ := by nlinarith
end RHHighZetaGrowth

theorem solution : ∀ t : ℝ, ‖riemannZeta (1/2+(t:ℂ)*Complex.I)‖≤3+|t| := RHHighZetaGrowth.critical_growth
