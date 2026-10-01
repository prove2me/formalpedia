-- Prove2me | solution 1 for SingleMachineSched.AlphaJSched.lemma_3_11
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T15:47:22.281987+00:00
-- url     : https://prove2.me/submissions/9d69760a-4624-4491-b6d6-aed5315e5719

import Definitions.Def_SingleMachineSched_AlphaJSched_DensityG
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Tactic
open MeasureTheory Set
private theorem exp_affine_integral (a b k u v : ℝ) (hab : a ≤ b) :
    (∫ t in Ioc a b,k*Real.exp t*(u*t+v))=
      k*(Real.exp b*(u*b+v-u)-Real.exp a*(u*a+v-u)) := by
  rw [← intervalIntegral.integral_of_le hab]
  have hd (t : ℝ) : HasDerivAt (fun t => k*(Real.exp t*(u*t+v-u))) (k*Real.exp t*(u*t+v)) t := by
    convert! (((Real.hasDerivAt_exp t).mul (((hasDerivAt_id t).const_mul u).add_const (v-u))).const_mul k) using 1
    · ext x
      simp only [Pi.mul_apply,id_eq]
      ring
    · simp only [id_eq]
      ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t) ((show Continuous (fun t : ℝ => k*Real.exp t*(u*t+v)) by fun_prop).intervalIntegrable a b)]
  ring

private theorem trunc_integral (a b δ k : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (H : ℝ → ℝ) :
    (∫ t in Ioc a b,(if 0 < t ∧ t ≤ δ then k*Real.exp t else 0)*H t)=
      ∫ t in Ioc a (min b δ),k*Real.exp t*H t := by
  have he : (fun t => (if 0 < t ∧ t ≤ δ then k*Real.exp t else 0)*H t)=
      (Ioc 0 δ).indicator (fun t => k*Real.exp t*H t) := by
    funext t
    simp only [Set.indicator,Ioc,mem_setOf_eq]
    split_ifs <;> simp
  rw [he,integral_indicator measurableSet_Ioc,Measure.restrict_restrict measurableSet_Ioc]
  congr 1
  apply congrArg (fun s : Set ℝ => volume.restrict s)
  ext t
  simp only [mem_inter_iff,mem_Ioc,lt_min_iff,le_min_iff]
  constructor
  · rintro ⟨⟨ht0,htδ⟩,hta,htb⟩
    exact ⟨hta,htb,htδ⟩
  · rintro ⟨hta,htb,htδ⟩
    exact ⟨⟨lt_of_le_of_lt ha hta,htδ⟩,hta,htb⟩

private theorem trunc_lower (η δ k : ℝ) (hη : 0 ≤ η) (hδ : 0 ≤ δ) (u v : ℝ) :
    (∫ t in (0 : ℝ)..η,(if 0 < t ∧ t ≤ δ then k*Real.exp t else 0)*(u*t+v))=
      k*(Real.exp (min η δ)*(u*min η δ+v-u)-(v-u)) := by
  rw [intervalIntegral.integral_of_le hη,trunc_integral 0 η δ k le_rfl hη]
  rw [exp_affine_integral 0 (min η δ) k u v (le_min hη hδ)]
  simp
private theorem trunc_upper (μ δ k : ℝ) (hμ : 0 ≤ μ) (hμ1 : μ ≤ 1) (hδ1 : δ ≤ 1) (u v : ℝ) :
    (∫ t in μ..1,(if 0 < t ∧ t ≤ δ then k*Real.exp t else 0)*(u*t+v))=
      if μ ≤ δ then k*(Real.exp δ*(u*δ+v-u)-Real.exp μ*(u*μ+v-u)) else 0 := by
  rw [intervalIntegral.integral_of_le hμ1,trunc_integral μ 1 δ k hμ hμ1,min_eq_right hδ1]
  by_cases h : μ ≤ δ
  · rw [if_pos h,exp_affine_integral μ δ k u v h]
  · rw [if_neg h,Set.Ioc_eq_empty_of_le (le_of_not_ge h)]
    simp

private theorem trunc_density_base (δ k : ℝ) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hk : 0 ≤ k) (hnorm : k*(Real.exp δ-1)=1) :
    ((∀ a,0 ≤ if 0 < a ∧ a ≤ δ then k*Real.exp a else 0) ∧
      (∫ a in (0 : ℝ)..1,if 0 < a ∧ a ≤ δ then k*Real.exp a else 0)=1) ∧
      ∀ η ∈ Icc (0 : ℝ) 1,
        (∫ a in (0 : ℝ)..η,(if 0 < a ∧ a ≤ δ then k*Real.exp a else 0)*(1+a-η)) ≤ k*η := by
  refine ⟨⟨?_,?_⟩,?_⟩
  · intro a
    split_ifs
    · exact mul_nonneg hk (Real.exp_pos a).le
    · exact le_rfl
  · have hh := trunc_lower 1 δ k (by norm_num) hδ 0 1
    simpa [min_eq_right hδ1,hnorm] using hh
  · intro η hη
    have hh := trunc_lower η δ k hη.1 hδ 1 (1-η)
    have he : (fun a : ℝ => (if 0 < a ∧ a ≤ δ then k*Real.exp a else 0)*(1+a-η))=
        (fun a => (if 0 < a ∧ a ≤ δ then k*Real.exp a else 0)*(1*a+(1-η))) := by funext a;ring
    rw [he,hh]
    have hm : min η δ ≤ η := min_le_left _ _
    have hn : k*Real.exp (min η δ)*(min η δ-η) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hk (Real.exp_pos _).le) (sub_nonpos.mpr hm)
    nlinarith

open SingleMachineSched.AlphaJSched

theorem solution (γ : ℝ)
    (hγ : 0 < γ ∧ γ < 1 ∧ γ+Real.log (2-γ)=Real.exp (-γ)*((2-γ)*Real.exp γ-1)) :
    ((∀ a,0 ≤ gDens γ a) ∧ ∫ a in Ioc (0 : ℝ) 1,gDens γ a=1) ∧
      (∀ η∈Icc (0 : ℝ) 1,∫ a in (0 : ℝ)..η,gDens γ a*(1+a-η) ≤ (cConst γ-1)*η) ∧
      (∀ μ∈Icc (0 : ℝ) 1,(1+Eg γ)*∫ a in μ..1,gDens γ a ≤ cConst γ*(1-μ)) := by
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
  have hb := trunc_density_base d k hd.le hd1 hk hn
  have hEg : 1+Eg γ=d*c := by
    have hh := trunc_lower 1 d k (by norm_num) hd.le 1 0
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
  · change (∫ a in Ioc (0 : ℝ) 1,(if 0 < a ∧ a ≤ d then k*Real.exp a else 0))=1
    simpa only [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hb.1.2
  · intro μ hμ
    have ht := trunc_upper μ d k hμ.1 hμ.2 hd1 0 1
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
