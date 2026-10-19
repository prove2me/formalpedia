-- Prove2me | solution 1 for QuantumParallelRepetition.exactSourceGlobalCatalystWinningEffect_tensor_quadratic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:16.465991+00:00
-- url     : https://prove2.me/submissions/c5349278-b250-4669-ad31-1a8c12efd2dc

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_matrixQuadraticExpectation_injective
import Theorems.Thm_QuantumParallelRepetition_residualIdentity_quadratic
import Theorems.Thm_QuantumParallelRepetition_exactSourceGlobalCatalystWinningEffect_compression

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
noncomputable section
open WithLp
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option maxRecDepth 2048
open QuantumParallelRepetition.ClassicalSampling
attribute [local instance] Classical.propDecidable
variable {X Y A B : Type}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
namespace QuantumParallelRepetition
theorem _root_.solution
    [DecidableEq A] [DecidableEq B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D)
    (e : ℕ) (residual_positive : 0 < e)
    (a₀ : A) (b₀ : B) (x : X) (y : Y) :
    quadraticExpectation
      (Matrix.toEuclideanCLM
        (n :=
          Fin (Fintype.card
            (ExactGlobalHistoryLocalIndex G n S D) * e) ×
          Fin (Fintype.card
            (ExactGlobalHistoryLocalIndex G n S D) * e))
        (𝕜 := ℂ)
        (exactSourceGlobalCatalystWinningEffect
          G n S D e a₀ b₀ x y))
      (tensorEmbezzlementTarget (n := e)
        (exactGlobalHistoryFinPsi G n S D r x y)) =
    quadraticExpectation
      (Matrix.toEuclideanCLM
        (n :=
          ExactGlobalHistoryLocalIndex G n S D ×
          ExactGlobalHistoryLocalIndex G n S D)
        (𝕜 := ℂ)
        (exactSourceGlobalWinningEffect
          G n S D a₀ b₀ x y))
      (exactGlobalHistoryVector G n S D r
        (exactPsi G n S D r x y)) := by
  classical
  let source := exactGlobalHistoryVector G n S D r
    (exactPsi G n S D r x y)
  let residual := embezzlementState e
  let tensor : EuclideanSpace ℂ
      ((ExactGlobalHistoryLocalIndex G n S D ×
        ExactGlobalHistoryLocalIndex G n S D) ×
       (Fin e × Fin e)) :=
    toLp 2 (fun q => source q.1 * residual q.2)
  let basis := exactSourceGlobalCatalystBasisEquiv G n S D e
  calc
    _ = quadraticExpectation
      (Matrix.toEuclideanCLM
        (n :=
          (ExactGlobalHistoryLocalIndex G n S D ×
            ExactGlobalHistoryLocalIndex G n S D) ×
          (Fin e × Fin e))
        (𝕜 := ℂ)
        ((exactSourceGlobalWinningEffect
          G n S D a₀ b₀ x y) ⊗ₖ
          (1 : Matrix (Fin e × Fin e) (Fin e × Fin e) ℂ)))
      tensor := by
        apply matrixQuadraticExpectation_injective
          basis basis.injective
        · intro i
          rcases i with ⟨⟨ia, ib⟩, ⟨ka, kb⟩⟩
          have alice_system :
              (finProdFinEquiv
                ((Fintype.equivFin
                  (ExactGlobalHistoryLocalIndex G n S D))
                  ia, ka)).divNat =
                (Fintype.equivFin
                  (ExactGlobalHistoryLocalIndex G n S D)) ia := by
            exact congrArg Prod.fst
              (Equiv.symm_apply_apply finProdFinEquiv
                ((Fintype.equivFin
                  (ExactGlobalHistoryLocalIndex G n S D)) ia, ka))
          have alice_residual :
              (finProdFinEquiv
                ((Fintype.equivFin
                  (ExactGlobalHistoryLocalIndex G n S D))
                  ia, ka)).modNat = ka := by
            exact congrArg Prod.snd
              (Equiv.symm_apply_apply finProdFinEquiv
                ((Fintype.equivFin
                  (ExactGlobalHistoryLocalIndex G n S D)) ia, ka))
          have bob_system :
              (finProdFinEquiv
                ((Fintype.equivFin
                  (ExactGlobalHistoryLocalIndex G n S D))
                  ib, kb)).divNat =
                (Fintype.equivFin
                  (ExactGlobalHistoryLocalIndex G n S D)) ib := by
            exact congrArg Prod.fst
              (Equiv.symm_apply_apply finProdFinEquiv
                ((Fintype.equivFin
                  (ExactGlobalHistoryLocalIndex G n S D)) ib, kb))
          have bob_residual :
              (finProdFinEquiv
                ((Fintype.equivFin
                  (ExactGlobalHistoryLocalIndex G n S D))
                  ib, kb)).modNat = kb := by
            exact congrArg Prod.snd
              (Equiv.symm_apply_apply finProdFinEquiv
                ((Fintype.equivFin
                  (ExactGlobalHistoryLocalIndex G n S D)) ib, kb))
          simp [basis, tensor, source, residual,
            exactSourceGlobalCatalystBasisEquiv,
            tensorEmbezzlementTarget,
            exactGlobalHistoryFinPsi,
            exactGlobalHistoryFinReindex,
            LinearIsometryEquiv.piLpCongrLeft_apply,
            Equiv.piCongrLeft'_apply,
            alice_system, alice_residual,
            bob_system, bob_residual]
        · intro j outside
          exact False.elim
            (outside (basis.symm j) (basis.apply_symm_apply j))
        · exact exactSourceGlobalCatalystWinningEffect_compression
            G n S D e a₀ b₀ x y
    _ = _ := residualIdentity_quadratic
      (exactSourceGlobalWinningEffect G n S D a₀ b₀ x y)
      source residual
      (embezzlementState_norm e residual_positive)
end QuantumParallelRepetition
