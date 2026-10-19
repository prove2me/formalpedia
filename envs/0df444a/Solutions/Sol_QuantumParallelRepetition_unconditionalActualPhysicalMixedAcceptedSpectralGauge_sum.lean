-- Prove2me | solution 1 for QuantumParallelRepetition.unconditionalActualPhysicalMixedAcceptedSpectralGauge_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:17.846829+00:00
-- url     : https://prove2.me/submissions/32906b08-4637-418f-a99c-56db73fbd432

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
attribute [local instance] Classical.propDecidable
namespace QuantumParallelRepetition
theorem _root_.solution
    {N d : ℕ}
    (f : DSVUniformDensityThresholdLocalIndex N d →
      DSVUniformDensityThresholdLocalIndex N d → ℂ) :
    (∑ i : Fin d, ∑ k : Fin N,
      ∑ j : Fin d, ∑ l : Fin N,
        f ⟨k, i⟩ ⟨l, j⟩) =
      ∑ x : DSVUniformDensityThresholdLocalIndex N d,
        ∑ y : DSVUniformDensityThresholdLocalIndex N d,
          f x y := by
  classical
  simp only [Fintype.sum_sigma]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
end QuantumParallelRepetition
