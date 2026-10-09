-- Prove2me | solution 1 for OCB2012.causal_inequality_violation
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-10-08T23:16:12.277673+00:00
-- url     : https://prove2.me/submissions/8b12bb0f-025e-413f-b3a4-7475fc3db330

import Mathlib
import Definitions.Def_PeresTerno_kraus_basics
import Definitions.Def_OCB2012_defs
import Theorems.Thm_OCB2012_W7_isProcessMatrix
import Theorems.Thm_OCB2012_protocol_pSucc

open Matrix
open scoped Kronecker ComplexOrder

namespace OCB2012Sol
open OCB2012

/-- The maximally mixed qubit state `𝟙/2`, used as Bob's (arbitrary) state for `b' = 1`. -/
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
theorem solution :
    ∃ (W : Matrix ((Qubit × Qubit) × (Qubit × Qubit)) ((Qubit × Qubit) × (Qubit × Qubit)) ℂ)
      (MA : Bool → Bool → Matrix (Qubit × Qubit) (Qubit × Qubit) ℂ)
      (MB : Bool → Bool → Bool → Matrix (Qubit × Qubit) (Qubit × Qubit) ℂ),
      IsProcessMatrix W ∧ IsAliceInstrument MA ∧ IsBobInstrument MB ∧
        3 / 4 < pSucc W MA MB := by
  obtain ⟨hξ, hη, hp⟩ := protocol_pSucc _ isDensityMatrix_half_one
  exact ⟨W7, ξ, η ((1 / 2 : ℂ) • 1), W7_isProcessMatrix, hξ, hη, hp ▸ three_quarters_lt⟩
