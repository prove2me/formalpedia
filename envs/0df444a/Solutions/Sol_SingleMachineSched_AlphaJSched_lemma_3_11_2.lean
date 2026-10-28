-- Prove2me | solution 2 for SingleMachineSched.AlphaJSched.lemma_3_11
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-26T06:12:17.478488+00:00
-- url     : https://prove2.me/submissions/e54ec82d-f828-4969-b026-805f6c187eb5

import Mathlib
import Theorems.Thm_TruncExpDensity_truncExp_isDensity_and_lower_bound
import Theorems.Thm_TruncExpDensity_integral_truncExp_affine_Ioc_zero
import Theorems.Thm_TruncExpDensity_integral_truncExp_affine_Ioc_one
import Definitions.Def_SingleMachineSched_AlphaJSched_DensityG

set_option autoImplicit false
set_option linter.unusedVariables false
open Set MeasureTheory SingleMachineSched.AlphaJSched

-- carved from submission 510cef8c-8e14-4ee8-8b48-e4ca3a7e7938, lines 2345-2409

theorem solution (γ : ℝ)
    (hγ : 0 < γ ∧ γ < 1 ∧ γ+Real.log (2-γ)=Real.exp (-γ)*((2-γ)*Real.exp γ-1)) :
    ((∀ a,0 ≤ gDens γ a) ∧ ∫ a in Set.Ioc (0 : ℝ) 1,gDens γ a=1) ∧
      (∀ η∈Set.Icc (0 : ℝ) 1,∫ a in (0 : ℝ)..η,gDens γ a*(1+a-η) ≤ (cConst γ-1)*η) ∧
      (∀ μ∈Set.Icc (0 : ℝ) 1,(1+Eg γ)*∫ a in μ..1,gDens γ a ≤ cConst γ*(1-μ)) := by
  let d := delta γ
  let c := cConst γ
  let k := c-1
  have hγ2 : 0 < 2-γ := by linarith [hγ.2.1]
  have hd : 0 < d := by
    dsimp [d,delta]
    have hh := Real.log_nonneg (show 1 ≤ 2-γ by linarith [hγ.2.1])
    linarith [hγ.1]
  have hem : Real.exp (-γ)*Real.exp γ=1 := by rw [← Real.exp_add];simp
  have hdrel : d=2-γ-Real.exp (-γ) := by
    change γ+Real.log (2-γ)=_
    rw [hγ.2.2]
    nlinarith [hem]
  have hd1 : d ≤ 1 := by
    have hh := Real.add_one_le_exp (-γ)
    rw [hdrel]
    linarith
  have hkform : k=Real.exp (-γ)/d := by dsimp [k,c,cConst,d];ring
  have hk : 0 ≤ k := by rw [hkform];positivity
  have hc : 0 ≤ c := by dsimp [c,cConst];positivity
  have he : Real.exp d=(2-γ)*Real.exp γ := by
    dsimp [d,delta]
    rw [Real.exp_add,Real.exp_log hγ2]
    ring
  have hdk : d*k=Real.exp (-γ) := by rw [hkform];field_simp
  have hne : Real.exp (-γ)*Real.exp d=2-γ := by rw [he];nlinarith [hem]
  have hn : k*(Real.exp d-1)=1 := by
    rw [hkform]
    apply (div_mul_eq_mul_div _ _ _).trans
    apply (div_eq_one_iff_eq hd.ne').mpr
    nlinarith [hdrel,hne]
  have hke : k*Real.exp d=c := by dsimp [k] at hn ⊢;nlinarith
  have hb := TruncExpDensity.truncExp_isDensity_and_lower_bound d k hd.le hd1 hk hn
  have hEg : 1+Eg γ=d*c := by
    have hh := TruncExpDensity.integral_truncExp_affine_Ioc_zero 1 d k (by norm_num) hd.le 1 0
    simp only [min_eq_right hd1,one_mul,add_zero,zero_sub] at hh
    have hI : Eg γ=∫ t in (0 : ℝ)..1,(if 0 < t ∧ t ≤ d then k*Real.exp t else 0)*t := by
      rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
      unfold Eg gDens
      apply integral_congr_ae
      filter_upwards [] with t
      ring
    rw [hI,hh]
    nlinarith [hke,hn]
  refine ⟨⟨hb.1.1,?_⟩,hb.2,?_⟩
  · change (∫ a in Set.Ioc (0 : ℝ) 1,(if 0 < a ∧ a ≤ d then k*Real.exp a else 0))=1
    simpa only [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hb.1.2
  · intro μ hμ
    have ht := TruncExpDensity.integral_truncExp_affine_Ioc_one μ d k hμ.1 hμ.2 hd1 0 1
    simp only [zero_mul,zero_add,sub_zero,mul_one] at ht
    change (1+Eg γ)*(∫ t in μ..1,(if 0 < t ∧ t ≤ d then k*Real.exp t else 0)) ≤ c*(1-μ)
    rw [ht,hEg]
    split_ifs with hμd
    · have hme : Real.exp (-γ)*Real.exp μ=Real.exp (μ-γ) := by rw [← Real.exp_add];congr 1;ring
      calc
        d*c*(k*(Real.exp d-Real.exp μ))=c*((d*k)*Real.exp d-(d*k)*Real.exp μ) := by ring
        _=c*((2-γ)-Real.exp (μ-γ)) := by rw [hdk,hne,hme]
        _ ≤ c*(1-μ) := mul_le_mul_of_nonneg_left (by have hh := Real.add_one_le_exp (μ-γ);linarith) hc
    · simp only [mul_zero]
      exact mul_nonneg hc (sub_nonneg.mpr hμ.2)
