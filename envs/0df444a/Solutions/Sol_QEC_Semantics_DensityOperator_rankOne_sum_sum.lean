-- Prove2me | solution 1 for QEC.Semantics.DensityOperator.rankOne_sum_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:38:21.933159+00:00
-- url     : https://prove2.me/submissions/3a7f9ff5-6dcb-4983-81c0-8fcf0d0ca93f

import Definitions.Def_QEC_Semantics_Entropy_FiniteDimensional
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditSubsystem
import Definitions.Def_QEC_Semantics_Entropy_Purification

set_option autoImplicit false
universe u
open QEC
open QEC.Semantics
open scoped BigOperators ComplexOrder TensorProduct
noncomputable section
open QEC.Semantics.DensityOperator
variable {H : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
omit [FiniteQuantumSystem H]
namespace QEC.Semantics.DensityOperator
theorem _root_.solution {ι : Type*} [Fintype ι] (a b : ι → H) :
    (InnerProductSpace.rankOne Complex (∑ i, a i) (∑ j, b j)).toLinearMap =
      ∑ i, ∑ j, (InnerProductSpace.rankOne Complex (a i) (b j)).toLinearMap := by
  ext x
  rw [LinearMap.sum_apply]
  simp_rw [LinearMap.sum_apply]
  change inner Complex (∑ j, b j) x • ∑ i, a i =
    ∑ i, ∑ j, inner Complex (b j) x • a i
  rw [sum_inner, Finset.sum_smul]
  rw [Finset.sum_comm]
  simp_rw [Finset.smul_sum]
end QEC.Semantics.DensityOperator
