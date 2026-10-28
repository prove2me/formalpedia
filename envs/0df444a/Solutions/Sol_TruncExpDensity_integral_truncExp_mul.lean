-- Prove2me | solution 1 for TruncExpDensity.integral_truncExp_mul
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-26T06:07:47.060249+00:00
-- url     : https://prove2.me/submissions/e47992e7-cd77-495c-8388-0837740301fe

import Mathlib

set_option autoImplicit false
set_option linter.unusedVariables false
open Set MeasureTheory

-- carved from submission 510cef8c-8e14-4ee8-8b48-e4ca3a7e7938, lines 1702-1720

theorem solution (a b δ k : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (H : ℝ → ℝ) :
    (∫ t in Set.Ioc a b,(if 0 < t ∧ t ≤ δ then k*Real.exp t else 0)*H t)=
      ∫ t in Set.Ioc a (min b δ),k*Real.exp t*H t := by
  have he : (fun t => (if 0 < t ∧ t ≤ δ then k*Real.exp t else 0)*H t)=
      (Set.Ioc 0 δ).indicator (fun t => k*Real.exp t*H t) := by
    funext t
    simp only [Set.indicator,Set.Ioc,mem_setOf_eq]
    split_ifs <;> simp
  rw [he,integral_indicator measurableSet_Ioc,Measure.restrict_restrict measurableSet_Ioc]
  congr 1
  apply congrArg (fun s : Set ℝ => volume.restrict s)
  ext t
  simp only [mem_inter_iff,Set.mem_Ioc,lt_min_iff,le_min_iff]
  constructor
  · rintro ⟨⟨ht0,htδ⟩,hta,htb⟩
    exact ⟨hta,htb,htδ⟩
  · rintro ⟨hta,htb,htδ⟩
    exact ⟨⟨lt_of_le_of_lt ha hta,htδ⟩,hta,htb⟩
