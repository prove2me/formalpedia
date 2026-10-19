-- Prove2me | solution 1 for QuantumParallelRepetition.exactSourceGlobalCatalystWinningEffect_compression
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:16.465991+00:00
-- url     : https://prove2.me/submissions/6d4fb509-d99f-45af-9557-ea1b0e39d3ee

import Mathlib
import Definitions.Def_QuantumParallelRepetition

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
    (D : Finset (Fin n)) (e : ℕ)
    (a₀ : A) (b₀ : B) (x : X) (y : Y)
    (i j :
      (ExactGlobalHistoryLocalIndex G n S D ×
       ExactGlobalHistoryLocalIndex G n S D) ×
      (Fin e × Fin e)) :
    exactSourceGlobalCatalystWinningEffect
        G n S D e a₀ b₀ x y
      (exactSourceGlobalCatalystBasisEquiv G n S D e i)
      (exactSourceGlobalCatalystBasisEquiv G n S D e j) =
      ((exactSourceGlobalWinningEffect G n S D a₀ b₀ x y) ⊗ₖ
        (1 : Matrix (Fin e × Fin e) (Fin e × Fin e) ℂ)) i j := by
  classical
  rcases i with ⟨⟨ia, ib⟩, ⟨ka, kb⟩⟩
  rcases j with ⟨⟨ja, jb⟩, ⟨la, lb⟩⟩
  by_cases alice_residual : ka = la
  · subst la
    by_cases bob_residual : kb = lb
    · subst lb
      simp only [exactSourceGlobalCatalystWinningEffect,
        exactSourceGlobalWinningEffect, Matrix.sum_apply,
        Matrix.kroneckerMap_apply,
        exactSourceGlobalCatalystBasisEquiv,
        Equiv.trans_apply, Equiv.prodCongr_apply,
        Equiv.prodProdProdComm_apply, Matrix.one_apply,
        ite_true, mul_one]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      split_ifs with winning
      · simp [Matrix.kroneckerMap_apply,
                    exactSourceGlobalCatalystAlicePOVM_effect_global,
          exactSourceGlobalCatalystBobPOVM_effect]
      · rfl
    · simp [exactSourceGlobalCatalystWinningEffect,
        exactSourceGlobalWinningEffect,
        exactSourceGlobalCatalystBasisEquiv,
        Matrix.sum_apply, Matrix.kroneckerMap_apply,                         bob_residual]
      apply Finset.sum_eq_zero
      intro a _
      apply Finset.sum_eq_zero
      intro b _
      split_ifs with winning
      · simp [Matrix.kroneckerMap_apply,
          exactSourceGlobalCatalystAlicePOVM_effect_global,
          exactSourceGlobalCatalystBobPOVM_effect,
          bob_residual]
      · rfl
  · simp [exactSourceGlobalCatalystWinningEffect,
      exactSourceGlobalWinningEffect,
      exactSourceGlobalCatalystBasisEquiv,
      Matrix.sum_apply, Matrix.kroneckerMap_apply,                   alice_residual]
    apply Finset.sum_eq_zero
    intro a _
    apply Finset.sum_eq_zero
    intro b _
    split_ifs with winning
    · simp [Matrix.kroneckerMap_apply,
        exactSourceGlobalCatalystAlicePOVM_effect_global,
        exactSourceGlobalCatalystBobPOVM_effect,
        alice_residual]
    · rfl
end QuantumParallelRepetition
