-- Prove2me | solution 1 for QuantumParallelRepetition.unconditionalActualFairSourceMatchedHistoryCleanedVector
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:19.890976+00:00
-- url     : https://prove2.me/submissions/9c92a973-0dbb-452f-95da-32720b7c47f4

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_unconditionalActualFairSourceMatchedHistoryGamma
import Theorems.Thm_QuantumParallelRepetition_unconditionalActualFairSourceMatchedHistoryPhi

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
    (D : Finset (Fin n)) (denominator : ℕ)
    (numerator : ExactLocalSamplerIndex X Y D →
      ExactHistoryFlag X Y A B D → ℕ)
    (nonempty : ∀ index,
      (rationalMarked denominator (numerator index)).Nonempty)
    {P N L m : ℕ} (Q : ℕ)
    (width : Fin 1 → ℝ) (schedule : Fin L → Fin 1)
    (UA UB : Fin P → Option ℕ →
      Matrix.unitaryGroup (Fin (N * m)) ℂ)
    (flag : ExactSourceSharedFlag X Y A B D denominator)
    (x : X) (y : Y)
    (matching :
      exactSourcePermutationMatched
        D denominator numerator nonempty (flag, (x, y)) = true)
    (j : Fin L) :
    let h := exactSourceAliceSampleTuple
      D denominator numerator nonempty (flag, (x, y))
    integratorActualC485CleanedVector
        (S := 1) (B := P) (N := N)
        (d := Fintype.card (ExactGlobalHistoryLocalIndex G n S D))
        (L := L) (m := m)
        Q width schedule
        (unconditionalExactFairGammaUnit G n S D h)
        (exactGlobalHistoryFinPhi G n S D h.2.2.2 h.2.2.1)
        UA UB j =
      integratorActualC485CleanedVector
        (S := 1) (B := P) (N := N)
        (d := Fintype.card (ExactGlobalHistoryLocalIndex G n S D))
        (L := L) (m := m)
        Q width schedule
        (unconditionalActualFairSourceAliceTarget
          G n S D denominator numerator nonempty flag x)
        (unconditionalActualFairSourceBobTarget
          G n S D denominator numerator nonempty flag y)
        UA UB j := by
  dsimp only
  exact congrArg₂
    (fun (u v : BipartiteUnitVector
        (Fintype.card (ExactGlobalHistoryLocalIndex G n S D))) =>
      integratorActualC485CleanedVector
        (S := 1) (B := P) (N := N)
        (d := Fintype.card (ExactGlobalHistoryLocalIndex G n S D))
        (L := L) (m := m)
        Q width schedule u v UA UB j)
    (unconditionalActualFairSourceMatchedHistoryGamma
      G n S D denominator numerator nonempty flag x y)
    (unconditionalActualFairSourceMatchedHistoryPhi
      G n S D denominator numerator nonempty flag x y matching)
end QuantumParallelRepetition
