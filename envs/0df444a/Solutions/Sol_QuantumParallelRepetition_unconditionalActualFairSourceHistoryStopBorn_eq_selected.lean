-- Prove2me | solution 1 for QuantumParallelRepetition.unconditionalActualFairSourceHistoryStopBorn_eq_selected
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:19.890976+00:00
-- url     : https://prove2.me/submissions/5166b5a5-8ed5-4cd6-9271-f74db669ac23

import Mathlib
import Definitions.Def_QuantumParallelRepetition

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
noncomputable section
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
open QuantumParallelRepetition.ClassicalSampling
namespace QuantumParallelRepetition
theorem _root_.solution
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (a₀ : A) (b₀ : B)
    {P N L m : ℕ} (Q : ℕ)
    (width : Fin 1 → ℝ) (schedule : Fin L → Fin 1)
    (UA UB : Fin P → Option ℕ →
      Matrix.unitaryGroup (Fin (N * m)) ℂ)
    (h : ExactLocallySampleableTuple X Y A B D)
    (j : Fin L) :
    unconditionalActualFairSourceHistoryStopBorn
        G n S D a₀ b₀ Q width schedule UA UB h j =
      unconditionalActualC485SelectedVerifierBorn G
        (integratorActualC485SelectedAlicePOVM
          G n S D a₀ P N m h.2.1)
        (integratorActualC485SelectedBobPOVM
          G n S D b₀ P N m h.2.2.1)
        h.2.1 h.2.2.1
        (integratorActualC485CleanedVector
          (S := 1) (B := P) (N := N)
          (d := Fintype.card
            (ExactGlobalHistoryLocalIndex G n S D))
          (L := L) (m := m)
          Q width schedule
          (unconditionalExactFairGammaUnit G n S D h)
          (exactGlobalHistoryFinPhi
            G n S D h.2.2.2 h.2.2.1)
          UA UB j) := by
  classical
  rfl
end QuantumParallelRepetition
