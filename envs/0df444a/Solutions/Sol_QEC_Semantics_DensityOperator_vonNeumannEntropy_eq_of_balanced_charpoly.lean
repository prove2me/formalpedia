-- Prove2me | solution 1 for QEC.Semantics.DensityOperator.vonNeumannEntropy_eq_of_balanced_charpoly
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:46:59.338863+00:00
-- url     : https://prove2.me/submissions/ff39d497-776a-4ec1-9716-ddf7fb8da477

import Definitions.Def_QEC_Semantics_Entropy_FiniteDimensional
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditSubsystem
import Definitions.Def_QEC_Semantics_Entropy_Purification
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
theorem _root_.solution {K : Type u}
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (rho : DensityOperator H) (sigma : DensityOperator K) (m n : Nat)
    (hcharpoly : (Polynomial.X : Polynomial Complex) ^ m * rho.toOperator.charpoly =
      (Polynomial.X : Polynomial Complex) ^ n * sigma.toOperator.charpoly) :
    rho.vonNeumannEntropy = sigma.vonNeumannEntropy := by
  have hrho : rho.toOperator.charpoly ≠ 0 :=
    (LinearMap.charpoly_monic rho.toOperator).ne_zero
  have hsigma : sigma.toOperator.charpoly ≠ 0 :=
    (LinearMap.charpoly_monic sigma.toOperator).ne_zero
  have hleft : (Polynomial.X : Polynomial Complex) ^ m * rho.toOperator.charpoly ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ Polynomial.X_ne_zero) hrho
  have hright : (Polynomial.X : Polynomial Complex) ^ n * sigma.toOperator.charpoly ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ Polynomial.X_ne_zero) hsigma
  have hroots := congrArg Polynomial.roots hcharpoly
  rw [Polynomial.roots_mul hleft, Polynomial.roots_mul hright,
    Polynomial.roots_X_pow, Polynomial.roots_X_pow] at hroots
  have hsum := congrArg (fun s : Multiset Complex =>
    ((s.map Complex.re).map entropyTerm).sum) hroots
  have hzero (q : Nat) : (q • ({0} : Multiset Real)).sum = 0 := by
    rw [Multiset.sum_nsmul, Multiset.sum_singleton, nsmul_zero]
  unfold vonNeumannEntropy finiteSpectrum
  have hsum' : 0 +
      ((rho.toOperator.charpoly.roots.map Complex.re).map entropyTerm).sum = 0 +
        ((sigma.toOperator.charpoly.roots.map Complex.re).map entropyTerm).sum := by
    simpa [Multiset.map_add, Multiset.map_nsmul, Multiset.sum_add, entropyTerm_zero,
      hzero] using hsum
  exact add_left_cancel hsum'
end QEC.Semantics.DensityOperator
