-- Prove2me | solution 1 for QEC.Semantics.FiniteKrausFamily.indexedConditionWithScalar_posSemidef_of_carrier_ne_bot
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:34:23.170682+00:00
-- url     : https://prove2.me/submissions/dd995d45-4d77-48cd-9d7a-02a7f0005295

import Definitions.Def_QEC_Semantics_Channels_KrausKnillLaflamme
import Definitions.Def_QEC_Semantics_Channels_ChoiKraus
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_toOperator
import Theorems.Thm_QEC_Semantics_OperatorMatrix_matrixUnit_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_apply
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_toOperator
attribute [local simp] QEC.Semantics.OperatorMatrix.matrixUnit_apply
attribute [local simp] QEC.Semantics.QuantumChannel.comp_apply
attribute [local simp] QEC.Semantics.QuantumChannel.id_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator



set_option autoImplicit false
universe u v w
open QEC
open QEC.Semantics
open scoped BigOperators ComplexOrder
noncomputable section
open QEC.Semantics.FiniteKrausFamily
variable {ι : Type v} [Fintype ι]
variable {κ : Type w} [Fintype κ]
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H]
namespace QEC.Semantics.FiniteKrausFamily
theorem _root_.solution
    {E : FiniteKrausFamily ι H H} {C : QuantumCode H}
    {scalar : ι → ι → Complex}
    (hC : C.carrier ≠ ⊥)
    (hKL : IndexedKnillLaflammeConditionWithScalar E C scalar) :
    (Matrix.of fun i j => scalar i j).PosSemidef := by
  classical
  rcases Submodule.exists_mem_ne_zero_of_ne_bot hC with ⟨z, hzC, hz_ne⟩
  let G : Matrix ι ι Complex := Matrix.gram Complex (fun i => E.operator i z)
  have hinner_ne : inner Complex z z ≠ 0 := by
    rw [inner_self_eq_norm_sq_to_K]
    have hz_norm_ne : ‖z‖ ≠ 0 := by
      simpa [norm_eq_zero] using hz_ne
    exact pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr hz_norm_ne)
  have hinner_nonneg : 0 ≤ inner Complex z z := by
    rw [inner_self_eq_norm_sq_to_K]
    positivity
  have hEq :
      (Matrix.of fun i j => scalar i j) = (inner Complex z z)⁻¹ • G := by
    ext i j
    have hij := hKL i j z hzC z hzC
    have hscalar :
        scalar i j =
          (inner Complex z z)⁻¹ * inner Complex (E.operator i z) (E.operator j z) := by
      rw [hij]
      field_simp [hinner_ne]
    simp [G, hscalar]
  rw [hEq]
  exact (Matrix.posSemidef_gram Complex (fun i => E.operator i z)).smul
    ((inv_nonneg).2 hinner_nonneg)
end QEC.Semantics.FiniteKrausFamily
