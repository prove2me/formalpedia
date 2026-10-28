-- Prove2me | solution 1 for TruncExpDensity.truncExp_isDensity_and_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-26T06:10:48.057907+00:00
-- url     : https://prove2.me/submissions/95edf434-9473-4b01-99a4-3a743b827f86

import Mathlib
import Theorems.Thm_TruncExpDensity_integral_truncExp_affine_Ioc_zero

set_option autoImplicit false
set_option linter.unusedVariables false
open Set MeasureTheory

-- carved from submission 510cef8c-8e14-4ee8-8b48-e4ca3a7e7938, lines 1736-1759

theorem solution (δ k : ℝ) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
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
  · have hh := TruncExpDensity.integral_truncExp_affine_Ioc_zero 1 δ k (by norm_num) hδ 0 1
    simpa [min_eq_right hδ1,hnorm] using hh
  · intro η hη
    have hh := TruncExpDensity.integral_truncExp_affine_Ioc_zero η δ k hη.1 hδ 1 (1-η)
    have he : (fun a : ℝ => (if 0 < a ∧ a ≤ δ then k*Real.exp a else 0)*(1+a-η))=
        (fun a => (if 0 < a ∧ a ≤ δ then k*Real.exp a else 0)*(1*a+(1-η))) := by funext a;ring
    rw [he,hh]
    have hm : min η δ ≤ η := min_le_left _ _
    have hn : k*Real.exp (min η δ)*(min η δ-η) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hk (Real.exp_pos _).le) (sub_nonpos.mpr hm)
    nlinarith
