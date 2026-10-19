-- Prove2me | solution 1 for QuantumParallelRepetition.unconditionalActualFairWeightedStoppedSuccess
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:18.584171+00:00
-- url     : https://prove2.me/submissions/bebe7045-1abb-4384-b0c5-45457ce83b6e

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_unconditionalActualFairCleanedRow_eq_stoppedSuccess

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
noncomputable section
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
attribute [local instance] Classical.propDecidable
namespace QuantumParallelRepetition
theorem _root_.solution
    {I : Type} [Fintype I]
    {S B N d L m : Nat}
    (weight : I → ℝ)
    (weight_normalized : (∑ h : I, weight h) = 1)
    (phases : 0 < B) (grid : 0 < N)
    (dimension : 0 < d) (harmonic : 0 < m)
    (width : Fin S → ℝ) (width_positive : ∀ s, 0 < width s)
    (schedule : Fin L → Fin S)
    (ξ ζ : I → BipartiteUnitVector d)
    (Q : Nat)
    (A C : Fin B → Option Nat →
      Matrix.unitaryGroup (Fin (N * m)) ℂ)
    (async terminal : ℝ)
    (asynchronous_bound :
      (∑ h : I, weight h *
        dSVDensityRationalHeterogeneousPhysicalStoppedAsynchronousMass
          N width schedule (ξ h) (ζ h)) ≤ async)
    (terminal_bound :
      (∑ h : I, weight h *
        dSVDensityRationalHeterogeneousPhysicalTerminalMass
          N width schedule (ξ h) (ζ h)) ≤ terminal) :
    1 - (async + terminal) ≤
      ∑ h : I, weight h *
        ∑ j : Fin L,
          ‖integratorActualC485CleanedVector
            Q width schedule (ξ h) (ζ h) A C j‖ ^ 2 := by
  have partition :
      (∑ h : I, weight h *
        dSVDensityRationalHeterogeneousPhysicalStoppedSuccessMass
          N width schedule (ξ h) (ζ h)) +
      (∑ h : I, weight h *
        dSVDensityRationalHeterogeneousPhysicalStoppedAsynchronousMass
          N width schedule (ξ h) (ζ h)) +
      (∑ h : I, weight h *
        dSVDensityRationalHeterogeneousPhysicalTerminalMass
          N width schedule (ξ h) (ζ h)) = 1 := by
    calc
      _ = ∑ h : I, weight h *
        (dSVDensityRationalHeterogeneousPhysicalStoppedSuccessMass
            N width schedule (ξ h) (ζ h) +
          dSVDensityRationalHeterogeneousPhysicalStoppedAsynchronousMass
            N width schedule (ξ h) (ζ h) +
          dSVDensityRationalHeterogeneousPhysicalTerminalMass
            N width schedule (ξ h) (ζ h)) := by
            simp_rw [mul_add, Finset.sum_add_distrib]
      _ = ∑ h : I, weight h := by
        apply Finset.sum_congr rfl
        intro h _
        rw [dSVDensityRationalHeterogeneousPhysicalStopped_mass_partition
          grid dimension width schedule (ξ h) (ζ h)]
        ring
      _ = 1 := weight_normalized
  simp_rw [unconditionalActualFairCleanedRow_eq_stoppedSuccess
    phases grid dimension harmonic width width_positive
    schedule _ _ Q A C]
  linarith
end QuantumParallelRepetition
