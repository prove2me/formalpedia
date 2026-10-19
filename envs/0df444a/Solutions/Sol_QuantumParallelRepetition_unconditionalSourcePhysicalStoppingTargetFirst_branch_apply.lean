-- Prove2me | solution 1 for QuantumParallelRepetition.unconditionalSourcePhysicalStoppingTargetFirst_branch_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:17.186359+00:00
-- url     : https://prove2.me/submissions/ae76ec90-3da1-4590-82ef-4a39e4b321f6

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_dSVDensityRationalHeterogeneousOriginalStoppedState_apply

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
    {S B N d L m : ℕ}
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d)
    (r s : Fin (L + 1))
    (φ ψ : DSVDensityRationalPublicMultiscalePhaseIndex S B)
    (a b : DSVUniformDensityIndependentHistoryLocalIndex
      (L + 1) N d)
    (i k : Fin m) :
    actualStoppingBranchVector
      (unconditionalSourcePhysicalStoppingTargetFirstStateEquiv
        S B N d L m
        (dSVDensityRationalHeterogeneousOriginalStoppedState
          S B N d L m width schedule ξ ζ)) r s
      (⟨(φ, a), i⟩, ⟨(ψ, b), k⟩) =
        ePRState
          (Fintype.card
            (DSVDensityRationalPublicMultiscalePhase S B))
          (φ, ψ) *
        dSVDensityRationalHeterogeneousActualPhysicalState
          N width schedule ξ ζ
          (⟨r, a⟩, ⟨s, b⟩) *
        embezzlementState m (i, k) := by
  change
    dSVDensityRationalHeterogeneousOriginalStoppedState
      S B N d L m width schedule ξ ζ
      (dSVDensityRationalPublicMultiscalePhaseTargetFirstIndexEquiv
        S B N d L m ((φ, ⟨r, a⟩), i),
       dSVDensityRationalPublicMultiscalePhaseTargetFirstIndexEquiv
        S B N d L m ((ψ, ⟨s, b⟩), k)) = _
  exact dSVDensityRationalHeterogeneousOriginalStoppedState_apply
    S B N d L m width schedule ξ ζ φ ψ ⟨r, a⟩ ⟨s, b⟩ i k
end QuantumParallelRepetition
