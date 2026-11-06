-- Prove2me | solution 1 for QEC.Semantics.DensityOperator.vonNeumannEntropy_eq_sum_of_orthonormal_eigenbasis
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:57:29.099294+00:00
-- url     : https://prove2.me/submissions/c31b9bac-7258-495d-8884-6edc750f6dfe

import Definitions.Def_QEC_Semantics_Entropy_FiniteDimensional
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditSubsystem
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Theorems.Thm_QEC_Semantics_DensityOperator_tensorDensity_toOperator
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_QuditSubsystem_additionalRetainedFactorSwap_apply_tmul
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Semantics.QuantumChannel.comp_apply
attribute [local simp] QEC.Semantics.QuantumChannel.id_apply
attribute [local simp] QEC.Semantics.QuditSubsystem.additionalRetainedFactorSwap_apply_tmul
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator


attribute [local simp] QEC.Semantics.DensityOperator.tensorDensity_toOperator

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
theorem _root_.solution {ι : Type*}
    [Fintype ι] [DecidableEq ι] (rho : DensityOperator H)
    (b : OrthonormalBasis ι Complex H) (e : ι → Real)
    (happly : ∀ i, rho.toOperator (b i) = (e i : Complex) • b i) :
    rho.vonNeumannEntropy = ∑ i, entropyTerm (e i) := by
  classical
  unfold vonNeumannEntropy finiteSpectrum
  rw [← LinearMap.charpoly_toMatrix rho.toOperator b.toBasis]
  have hmatrix : LinearMap.toMatrix b.toBasis b.toBasis rho.toOperator =
      Matrix.diagonal fun i => (e i : Complex) := by
    ext i j
    rw [LinearMap.toMatrix_apply]
    change b.repr (rho.toOperator (b j)) i = _
    rw [happly]
    rw [map_smul]
    change (e j : Complex) * b.repr (b j) i = _
    rw [OrthonormalBasis.repr_apply_apply]
    by_cases hij : i = j
    · subst j
      simp [Matrix.diagonal]
    · simp [Matrix.diagonal, b.inner_eq_ite, hij]
  rw [hmatrix, Matrix.charpoly_diagonal]
  rw [Polynomial.roots_prod _ _ (by
    simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero])]
  simp
end QEC.Semantics.DensityOperator
