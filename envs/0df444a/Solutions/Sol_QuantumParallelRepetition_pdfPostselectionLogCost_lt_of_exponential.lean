-- Prove2me | solution 1 for QuantumParallelRepetition.pdfPostselectionLogCost_lt_of_exponential
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:19.17122+00:00
-- url     : https://prove2.me/submissions/10289646-f8d7-475a-8f6b-b839d304eea2

import Mathlib
import Definitions.Def_QuantumParallelRepetition

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
noncomputable section
namespace QuantumParallelRepetition
theorem _root_.solution
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (G : Game X Y A B) (n : ℕ)
    (S : Strategy (G.repeat n)) (D : Finset (Fin n))
    (d : ℝ)
    (above : Real.exp (-d * (n : ℝ)) <
      repeatedPostselectionMass G n S D) :
    postselectionLogCost G n S D < d * (n : ℝ) := by
  have logarithm := Real.log_lt_log (Real.exp_pos (-d * (n : ℝ))) above
  rw [Real.log_exp] at logarithm
  unfold postselectionLogCost
  rw [one_div, Real.log_inv]
  linarith
end QuantumParallelRepetition
