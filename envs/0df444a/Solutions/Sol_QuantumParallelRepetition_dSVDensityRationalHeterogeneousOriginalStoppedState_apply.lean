-- Prove2me | solution 1 for QuantumParallelRepetition.dSVDensityRationalHeterogeneousOriginalStoppedState_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:17.186359+00:00
-- url     : https://prove2.me/submissions/3a4e4489-0d3a-4685-8e3a-5d67a83f988a

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_dSVDensityRationalHeterogeneousOriginalSameStopSigmaSource_apply
import Theorems.Thm_QuantumParallelRepetition_dSVDensityRationalHeterogeneousOriginalSameStopSigmaSource_eq_stopped

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
noncomputable section
open WithLp
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
namespace QuantumParallelRepetition
theorem _root_.solution
    (S B N d L m : ℕ)
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d)
    (φ ψ : DSVDensityRationalPublicMultiscalePhaseIndex S B)
    (a b : DSVUniformDensityThresholdWholeHistoryLocalIndex N d L)
    (i j : Fin m) :
    dSVDensityRationalHeterogeneousOriginalStoppedState
        S B N d L m width schedule ξ ζ
        (dSVDensityRationalPublicMultiscalePhaseTargetFirstIndexEquiv
            S B N d L m ((φ, a), i),
         dSVDensityRationalPublicMultiscalePhaseTargetFirstIndexEquiv
            S B N d L m ((ψ, b), j)) =
      ePRState
          (Fintype.card
            (DSVDensityRationalPublicMultiscalePhase S B))
          (φ, ψ) *
        dSVDensityRationalHeterogeneousActualPhysicalState
          N width schedule ξ ζ (a, b) *
        embezzlementState m (i, j) := by
  rw [←
    dSVDensityRationalHeterogeneousOriginalSameStopSigmaSource_eq_stopped]
  exact
    dSVDensityRationalHeterogeneousOriginalSameStopSigmaSource_apply
      S B N d L m width schedule ξ ζ φ ψ a b i j
end QuantumParallelRepetition
