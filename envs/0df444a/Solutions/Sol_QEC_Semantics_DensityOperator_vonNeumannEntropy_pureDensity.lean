-- Prove2me | solution 1 for QEC.Semantics.DensityOperator.vonNeumannEntropy_pureDensity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:59:28.407067+00:00
-- url     : https://prove2.me/submissions/5a4fbd31-43aa-4884-a1cb-5bf5b0b3d09d

import Definitions.Def_QEC_Semantics_Entropy_FiniteDimensional
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditSubsystem
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Theorems.Thm_QEC_Semantics_DensityOperator_pureDensity_balanced_charpoly
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
theorem _root_.solution (psi : H) (hpsi : ‖psi‖ ^ 2 = 1) :
    (pureDensity psi hpsi).vonNeumannEntropy = 0 := by
  have hpure : (pureDensity psi hpsi).toOperator.charpoly ≠ 0 :=
    (LinearMap.charpoly_monic (pureDensity psi hpsi).toOperator).ne_zero
  have hleft : (Polynomial.X : Polynomial Complex) *
      (pureDensity psi hpsi).toOperator.charpoly ≠ 0 :=
    mul_ne_zero Polynomial.X_ne_zero hpure
  have hright : (Polynomial.X : Polynomial Complex) ^ (Module.finrank Complex H) *
      (Polynomial.X - 1) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ Polynomial.X_ne_zero) (Polynomial.X_sub_C_ne_zero 1)
  have hroots := congrArg Polynomial.roots (pureDensity_balanced_charpoly psi hpsi)
  rw [Polynomial.roots_mul hleft, Polynomial.roots_X,
    Polynomial.roots_mul hright, Polynomial.roots_X_pow] at hroots
  have hXone : (Polynomial.X - 1 : Polynomial Complex).roots = {1} := by
    simpa using (Polynomial.roots_X_sub_C (1 : Complex))
  rw [hXone] at hroots
  have hsum := congrArg (fun s : Multiset Complex =>
    ((s.map Complex.re).map entropyTerm).sum) hroots
  have hzero (q : Nat) : (q • ({0} : Multiset Real)).sum = 0 := by
    rw [Multiset.sum_nsmul, Multiset.sum_singleton, nsmul_zero]
  unfold vonNeumannEntropy finiteSpectrum
  simpa [Multiset.map_add, Multiset.map_nsmul, Multiset.sum_add, entropyTerm_zero,
    entropyTerm_one, hzero] using hsum
end QEC.Semantics.DensityOperator
