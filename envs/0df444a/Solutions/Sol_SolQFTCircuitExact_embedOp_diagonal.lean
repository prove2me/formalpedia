-- Prove2me | solution 1 for SolQFTCircuitExact.embedOp_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T19:39:36.828991+00:00
-- url     : https://prove2.me/submissions/0db8ea95-9c54-4766-9871-0e06e7e891dd

import Definitions.Def_QAlgorithms_Defs_Fourier
import Mathlib
set_option autoImplicit false
open QAlgorithms
open scoped Matrix BigOperators
namespace SolQFTCircuitExact
end SolQFTCircuitExact
open SolQFTCircuitExact

theorem solution {k n : ℕ} (d : Qubits k → ℂ) (w : Fin k ↪ Fin n) :
    embedOp (Matrix.diagonal d) w = Matrix.diagonal (fun y => d (y ∘ w)) := by
  ext y z
  simp only [embedOp, Matrix.of_apply, Matrix.diagonal_apply]
  by_cases hyz : y = z
  · subst hyz
    simp
  · rw [if_neg hyz]
    split_ifs with h1 h2
    · exfalso
      apply hyz
      funext a
      by_cases ha : a ∈ Set.range w
      · rcases ha with ⟨i, rfl⟩
        exact congrFun h2 i
      · exact h1 a ha
    · rfl
    · rfl
