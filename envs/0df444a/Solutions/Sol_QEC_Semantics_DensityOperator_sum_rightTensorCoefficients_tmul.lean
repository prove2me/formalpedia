-- Prove2me | solution 1 for QEC.Semantics.DensityOperator.sum_rightTensorCoefficients_tmul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:47:12.218694+00:00
-- url     : https://prove2.me/submissions/9ea4f9de-b68a-43ac-8f7a-6376a1b89650

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
    (b : OrthonormalBasis (Fin (Module.finrank Complex K)) Complex K)
    (psi : CompositeSystem H K) :
    ∑ j, rightTensorCoefficients b psi j ⊗ₜ[Complex] b j = psi := by
  classical
  let a : Fin (Module.finrank Complex K) →₀ H := rightTensorCoefficients b psi
  have hrepr := (TensorProduct.equivFinsuppOfBasisRight b.toBasis).symm_apply_apply psi
  change (∑ j, a j ⊗ₜ[Complex] b j) = psi
  rw [TensorProduct.equivFinsuppOfBasisRight_symm_apply] at hrepr
  rw [← hrepr]
  rw [Finsupp.sum]
  symm
  apply Finset.sum_subset
  · exact Finset.subset_univ _
  · intro j _ hj
    change j ∉ a.support at hj
    have hzero : a j = 0 := by
      simpa only [Finsupp.mem_support_iff, not_not] using hj
    change a j ⊗ₜ[Complex] b j = 0
    simp [hzero]
end QEC.Semantics.DensityOperator
