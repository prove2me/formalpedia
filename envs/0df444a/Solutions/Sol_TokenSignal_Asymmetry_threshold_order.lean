-- Prove2me | solution 1 for TokenSignal.Asymmetry.threshold_order
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-30T20:04:29.570886+00:00
-- url     : https://prove2.me/submissions/2fd5b5b2-40de-4aee-865b-fd08ae9b93c0

import Mathlib
import Definitions.Def_TokenSignal_Asymmetry_Model
open TokenSignal.Asymmetry

theorem solution(P : Params) (hS : P.Standing) (j : Ty) :
    αbar P .token j < αbar P .equity j := by
  obtain ⟨hγ, hσ, hμ, hC, hI, hI2⟩ := hS
  have hER : ∀ j, ER P j = P.μ j / 4 := by
    intro j; unfold ER revLaw; rw [MeasureTheory.integral_div]; congr 1; exact ProbabilityTheory.integral_id_gaussianReal
  have hpos : ∀ j, 0 < P.μ j / 4 - P.C := by
    intro j; cases j <;> simp only [Params.μ] <;> linarith
  show P.I / ER P j < P.I / (ER P j - P.C)
  rw [hER]
  exact div_lt_div_of_pos_left hI (hpos j) (by linarith)
