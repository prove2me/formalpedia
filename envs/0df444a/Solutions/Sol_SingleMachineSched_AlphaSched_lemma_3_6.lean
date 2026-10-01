-- Prove2me | solution 1 for SingleMachineSched.AlphaSched.lemma_3_6
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T15:45:52.856367+00:00
-- url     : https://prove2.me/submissions/c442b902-6d2e-49b5-87e5-a746c8fcfed6

import Definitions.Def_SingleMachineSched_AlphaSched_Density
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

open SingleMachineSched.AlphaSched

theorem solution (γ : ℝ)
    (hγ : 0 < γ ∧ γ < 1 ∧ 1-γ^2/(1+γ)=γ+Real.log (1+γ)) :
    ((∀ a,0 ≤ fDens γ a) ∧ ∫ a in (0 : ℝ)..1,fDens γ a=1) ∧
      (∀ η∈Icc (0 : ℝ) 1,∫ a in (0 : ℝ)..η,fDens γ a*(1+a-η) ≤ (cConst γ-1)*η) ∧
      (∀ μ∈Icc (0 : ℝ) 1,∫ a in μ..1,fDens γ a*(1+a) ≤ cConst γ*(1-μ)) := by
  let δ := deltaConst γ
  let c := cConst γ
  let k := c-1
  have hγp : 0 < 1+γ := by linarith [hγ.1]
  have hd : 0 < 1+γ-Real.exp (-γ) := by
    have hh : Real.exp (-γ) < 1 := Real.exp_lt_one_iff.mpr (by linarith [hγ.1])
    linarith [hγ.1]
  have hδ : 0 ≤ δ := by
    dsimp [δ,deltaConst]
    have hh : γ^2 ≤ 1+γ := by nlinarith [mul_pos hγ.1 (sub_pos.mpr hγ.2.1)]
    have he := (div_le_one hγp).mpr hh
    linarith
  have hδ1 : δ ≤ 1 := by
    dsimp [δ,deltaConst]
    exact sub_le_self _ (div_nonneg (sq_nonneg _) hγp.le)
  have hkform : k=Real.exp (-γ)/(1+γ-Real.exp (-γ)) := by
    dsimp [k,c,cConst]
    field_simp
    ring
  have hk : 0 ≤ k := by rw [hkform];positivity
  have hc : 0 ≤ c := by dsimp [c,cConst];exact div_nonneg hγp.le hd.le
  have heδ : Real.exp δ=(1+γ)*Real.exp γ := by
    change Real.exp (1-γ^2/(1+γ))=_
    rw [hγ.2.2,Real.exp_add,Real.exp_log hγp]
    ring
  have hem : Real.exp (-γ)*Real.exp γ=1 := by rw [← Real.exp_add];simp
  have hke : k*Real.exp δ=c := by
    rw [hkform,heδ]
    dsimp [c,cConst]
    field_simp
    nlinarith [hem]
  have hkg : k*Real.exp γ*(1+γ)=c := by rw [← hke,heδ];ring
  have hn : k*(Real.exp δ-1)=1 := by dsimp [k] at hke ⊢;nlinarith
  have hbase := trunc_density_base δ k hδ hδ1 hk hn
  refine ⟨?_,?_,?_⟩
  · exact hbase.1
  · exact hbase.2
  · intro μ hμ
    have hh := trunc_upper μ δ k hμ.1 hμ.2 hδ1 1 1
    have he : (∫ a in μ..1,fDens γ a*(1+a))=
        if μ ≤ δ then k*(δ*Real.exp δ-μ*Real.exp μ) else 0 := by
      change (∫ a in μ..1,(if 0 < a ∧ a ≤ δ then k*Real.exp a else 0)*(1+a))=_
      convert hh using 1 <;> simp only [one_mul,add_sub_cancel_right] <;> ring
    rw [he]
    split_ifs with hμδ
    · have htan : Real.exp γ*(1+μ-γ) ≤ Real.exp μ := by
        have hh := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (μ-γ)) (Real.exp_pos γ).le
        have he : Real.exp γ*Real.exp (μ-γ)=Real.exp μ := by rw [← Real.exp_add];congr 1;ring
        rw [he] at hh
        nlinarith
      have htan' : Real.exp γ*((1+γ)*μ-γ^2) ≤ μ*Real.exp μ := by
        calc
          _ ≤ μ*(Real.exp γ*(1+μ-γ)) := by nlinarith [mul_nonneg (Real.exp_pos γ).le (sq_nonneg (μ-γ))]
          _ ≤ _ := mul_le_mul_of_nonneg_left htan hμ.1
      have hcδ : k*Real.exp γ*γ^2=c*(1-δ) := by
        have he : 1-δ=γ^2/(1+γ) := by dsimp [δ,deltaConst];ring
        rw [he,← hkg]
        field_simp
      have hbound := mul_le_mul_of_nonneg_left htan' hk
      nlinarith [hkg,hcδ,hke]
    · exact mul_nonneg hc (sub_nonneg.mpr hμ.2)
