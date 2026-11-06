-- Prove2me | solution 1 for QEC.Semantics.FiniteKrausFamily.indexedConditionWithScalar_isHermitian_of_carrier_ne_bot
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:44:18.325998+00:00
-- url     : https://prove2.me/submissions/8b498283-25c3-4ca1-8760-b6630eec1816

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
    (Matrix.of fun i j => scalar i j).IsHermitian := by
  classical
  rcases Submodule.exists_mem_ne_zero_of_ne_bot hC with ⟨z, hzC, hz_ne⟩
  apply Matrix.IsHermitian.ext
  intro i j
  have hij := hKL i j z hzC z hzC
  have hji := hKL j i z hzC z hzC
  have hinner_ne : inner Complex z z ≠ 0 := by
    rw [inner_self_eq_norm_sq_to_K]
    have hz_norm_ne : ‖z‖ ≠ 0 := by
      simpa [norm_eq_zero] using hz_ne
    exact pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr hz_norm_ne)
  have hstar :
      star (inner Complex (E.operator j z) (E.operator i z)) =
        inner Complex (E.operator i z) (E.operator j z) := by
    simp
  have hscalar :
      star (scalar j i * inner Complex z z) =
        scalar i j * inner Complex z z := by
    rw [← hji, hstar, hij]
  have hinner_self : star (inner Complex z z) = inner Complex z z := by
    simp
  rw [star_mul, hinner_self] at hscalar
  have hscalar' :
      star (scalar j i) * inner Complex z z =
        scalar i j * inner Complex z z := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using hscalar
  exact mul_right_cancel₀ hinner_ne hscalar'
end QEC.Semantics.FiniteKrausFamily
