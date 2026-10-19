-- Prove2me | solution 1 for QuantumParallelRepetition.unconditionalActualC485FairSourceDiagonalWork_row
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:18.584171+00:00
-- url     : https://prove2.me/submissions/be85af3b-b98e-4a76-b71a-4dc5f21f61fb

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_unconditionalActualC485NormalizedDiagonalWork_mass_sum_le_one

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
noncomputable section
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
namespace QuantumParallelRepetition
theorem _root_.solution
    {X Y A B : Type*}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    {w : ℝ} {N P L m : ℕ}
    (width : 0 < w) (grid : 0 < N)
    (dimension :
      0 < Fintype.card (ExactGlobalHistoryLocalIndex G n S D))
    (phases : 0 < P) (harmonic : 0 < m)
    (schedule : Fin L → Fin 1)
    (u : ExactLocallySampleableTuple X Y A B D) :
    (∑ j : Fin L,
      ‖unconditionalActualC485FairSourceDiagonalWork
          G n S D w N P schedule u j‖ ^ 2) ≤ 1 := by
  exact unconditionalActualC485NormalizedDiagonalWork_mass_sum_le_one
    (S := 1) (B := P) (N := N)
    (d := Fintype.card (ExactGlobalHistoryLocalIndex G n S D))
    (L := L) (m := m)
    phases grid dimension harmonic (fun _ : Fin 1 => w)
    (fun _ => width) schedule
    (unconditionalExactFairGammaUnit G n S D u)
    (exactGlobalHistoryFinPhi G n S D u.2.2.2 u.2.2.1)
end QuantumParallelRepetition
