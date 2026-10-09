-- Prove2me | solution 1 for OCB2012.W7_not_causallySeparable
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-10-08T23:16:13.743266+00:00
-- url     : https://prove2.me/submissions/77dba168-ac9b-4730-9be7-cb214d02eb8e

import Mathlib
import Definitions.Def_PeresTerno_kraus_basics
import Definitions.Def_OCB2012_defs
import Theorems.Thm_OCB2012_pSucc_le_of_causallySeparable
import Theorems.Thm_OCB2012_protocol_pSucc

open Matrix
open scoped Kronecker ComplexOrder

namespace OCB2012Sol
open OCB2012

lemma isDensityMatrix_half_one :
    PeresTerno.IsDensityMatrix ((1 / 2 : ℂ) • (1 : Matrix Qubit Qubit ℂ)) := by
  refine ⟨PosSemidef.one.smul ?_, ?_⟩
  · rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring]
    exact Complex.zero_le_real.mpr (by norm_num)
  · rw [trace_smul, trace_one]; simp

lemma three_quarters_lt : (3 / 4 : ℝ) < (2 + Real.sqrt 2) / 4 := by
  have : (1 : ℝ) < Real.sqrt 2 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  linarith

end OCB2012Sol

open OCB2012 OCB2012Sol in
theorem solution : ¬ IsCausallySeparable W7 := by
  intro hW
  obtain ⟨hξ, hη, hp⟩ := protocol_pSucc _ isDensityMatrix_half_one
  have h := pSucc_le_of_causallySeparable W7 hW ξ hξ _ hη
  rw [hp] at h
  linarith [three_quarters_lt]
