-- Prove2me | solution 1 for QEC.Semantics.DensityOperator.vonNeumannEntropy_tensorDensity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:01:32.279192+00:00
-- url     : https://prove2.me/submissions/f5c64c9e-bece-4aa3-a41d-7963b1885447

import Definitions.Def_QEC_Semantics_Entropy_FiniteDimensional
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditSubsystem
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Theorems.Thm_QEC_Semantics_DensityOperator_vonNeumannEntropy_tensorDensity_eq_double_sum
import Theorems.Thm_QEC_Semantics_DensityOperator_entropyTerm_mul
import Theorems.Thm_QEC_Semantics_DensityOperator_spectralEigenvalues_nonnegative
import Theorems.Thm_QEC_Semantics_DensityOperator_spectralEigenvalues_sum_eq_one
import Theorems.Thm_QEC_Semantics_DensityOperator_vonNeumannEntropy_eq_sum_spectralEigenvalues


set_option autoImplicit false
universe u
open QEC
open QEC.Semantics
open scoped BigOperators ComplexOrder TensorProduct
noncomputable section
open QEC.Semantics.DensityOperator
variable {H : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
namespace QEC.Semantics.DensityOperator
theorem _root_.solution {K : Type u}
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (rho : DensityOperator H) (sigma : DensityOperator K) :
    (tensorDensity rho sigma).vonNeumannEntropy =
      rho.vonNeumannEntropy + sigma.vonNeumannEntropy := by
  rw [vonNeumannEntropy_tensorDensity_eq_double_sum,
    rho.vonNeumannEntropy_eq_sum_spectralEigenvalues,
    sigma.vonNeumannEntropy_eq_sum_spectralEigenvalues]
  have hterm (i : Fin (Module.finrank Complex H))
      (j : Fin (Module.finrank Complex K)) :
      entropyTerm (rho.spectralEigenvalues i * sigma.spectralEigenvalues j) =
        sigma.spectralEigenvalues j * entropyTerm (rho.spectralEigenvalues i) +
          rho.spectralEigenvalues i * entropyTerm (sigma.spectralEigenvalues j) := by
    exact entropyTerm_mul _ _ (rho.spectralEigenvalues_nonnegative i)
      (sigma.spectralEigenvalues_nonnegative j)
  simp_rw [hterm]
  have hfirst :
      (∑ i, ∑ j, sigma.spectralEigenvalues j * entropyTerm (rho.spectralEigenvalues i)) =
        (∑ j, sigma.spectralEigenvalues j) *
          (∑ i, entropyTerm (rho.spectralEigenvalues i)) := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum]
    rw [← Finset.sum_mul]
  have hsecond :
      (∑ i, ∑ j, rho.spectralEigenvalues i * entropyTerm (sigma.spectralEigenvalues j)) =
        (∑ i, rho.spectralEigenvalues i) *
          (∑ j, entropyTerm (sigma.spectralEigenvalues j)) := by
    simp_rw [← Finset.mul_sum]
    rw [← Finset.sum_mul]
  simp_rw [Finset.sum_add_distrib]
  rw [hfirst, hsecond,
    rho.spectralEigenvalues_sum_eq_one, sigma.spectralEigenvalues_sum_eq_one]
  ring
end QEC.Semantics.DensityOperator
