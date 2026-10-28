-- Prove2me | solution 2 for SingleMachineSched.AlphaSched.lemma_3_6
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-26T06:12:16.883799+00:00
-- url     : https://prove2.me/submissions/31d13855-9eaf-4b69-ac9c-9d6009a0305b

import Mathlib
import Theorems.Thm_TruncExpDensity_truncExp_isDensity_and_lower_bound
import Theorems.Thm_TruncExpDensity_integral_truncExp_affine_Ioc_one
import Definitions.Def_SingleMachineSched_AlphaSched_Density

set_option autoImplicit false
set_option linter.unusedVariables false
open Set MeasureTheory SingleMachineSched.AlphaSched

-- carved from submission 510cef8c-8e14-4ee8-8b48-e4ca3a7e7938, lines 1760-1826

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
  have hbase := TruncExpDensity.truncExp_isDensity_and_lower_bound δ k hδ hδ1 hk hn
  refine ⟨?_,?_,?_⟩
  · exact hbase.1
  · exact hbase.2
  · intro μ hμ
    have hh := TruncExpDensity.integral_truncExp_affine_Ioc_one μ δ k hμ.1 hμ.2 hδ1 1 1
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
