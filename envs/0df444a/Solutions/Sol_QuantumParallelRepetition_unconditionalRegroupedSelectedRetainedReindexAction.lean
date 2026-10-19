-- Prove2me | solution 1 for QuantumParallelRepetition.unconditionalRegroupedSelectedRetainedReindexAction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:17.846829+00:00
-- url     : https://prove2.me/submissions/8c2650a4-fd61-4532-8f9c-b827ea11f8bf

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
namespace QuantumParallelRepetition
theorem _root_.solution
    {κ ι τ δ : Type}
    [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    [Fintype τ] [DecidableEq τ]
    [Fintype δ] [DecidableEq δ]
    (e : κ ≃ ι × τ)
    (workEquiv : τ × τ ≃ δ)
    (U V : Matrix.unitaryGroup ι ℂ)
    (z : EuclideanSpace ℂ (κ × κ)) :
    let regroup :=
      (unconditionalSelectedRetainedBilateralRegroup ι τ).trans
        (Equiv.prodCongr (Equiv.refl (ι × ι)) workEquiv)
    let sigma :=
      (Equiv.prodComm ι τ).trans (Equiv.sigmaEquivProd τ ι).symm
    let localEquiv := e.trans sigma
    let A := unconditionalSourceFixedPureStoppedSigmaReindexedUnitary
      localEquiv.symm (coherentSharedRandomControlledUnitary
        (fun _ : τ => U))
    let B := unconditionalSourceFixedPureStoppedSigmaReindexedUnitary
      localEquiv.symm (coherentSharedRandomControlledUnitary
        (fun _ : τ => V))
    let state := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
      ((Equiv.prodCongr e e).trans regroup)
    state
      (toLp 2
        ((((A : Matrix κ κ ℂ) ⊗ₖ
          (B : Matrix κ κ ℂ)).mulVec (ofLp z)))) =
      unconditionalMixedConjugateSelectedBranchLocalAction U V
        (state z) := by
  classical
  dsimp
  ext ⟨⟨i, j⟩, c⟩
  have reindex (f : κ × κ → ℂ) :
      (∑ p : κ × κ, f p) =
        ∑ p : (ι × τ) × (ι × τ),
          f (e.symm p.1, e.symm p.2) := by
    simpa using
      (Equiv.sum_comp (Equiv.prodCongr e e)
        (fun p : (ι × τ) × (ι × τ) =>
          f (e.symm p.1, e.symm p.2)))
  change
    (∑ p : κ × κ,
      (unconditionalSourceFixedPureStoppedSigmaReindexedUnitary
          (((Equiv.sigmaEquivProd τ ι).trans
            (Equiv.prodComm τ ι)).trans e.symm)
          (coherentSharedRandomControlledUnitary
            (fun _ : τ => U)) : Matrix κ κ ℂ)
          (e.symm (i, (workEquiv.symm c).1)) p.1 *
        (unconditionalSourceFixedPureStoppedSigmaReindexedUnitary
          (((Equiv.sigmaEquivProd τ ι).trans
            (Equiv.prodComm τ ι)).trans e.symm)
          (coherentSharedRandomControlledUnitary
            (fun _ : τ => V)) : Matrix κ κ ℂ)
          (e.symm (j, (workEquiv.symm c).2)) p.2 * z p) = _
  rw [reindex]
  simp [unconditionalSourceFixedPureStoppedSigmaReindexedUnitary,
    coherentSharedRandomControlledUnitary,
    unconditionalSelectedRetainedBilateralRegroup,
    unconditionalMixedConjugateSelectedBranchLocalAction,
    unconditionalMixedConjugateSelectedBranchUnitary,
    Matrix.mulVec, dotProduct,
    Matrix.blockDiagonal'_apply, Matrix.one_apply,
    Matrix.kroneckerMap_apply, LinearIsometryEquiv.piLpCongrLeft_apply,
    Equiv.piCongrLeft', Fintype.sum_prod_type, mul_assoc]
end QuantumParallelRepetition
