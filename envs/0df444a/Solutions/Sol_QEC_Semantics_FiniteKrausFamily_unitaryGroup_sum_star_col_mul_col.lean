-- Prove2me | solution 1 for QEC.Semantics.FiniteKrausFamily.unitaryGroup_sum_star_col_mul_col
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:34:51.037044+00:00
-- url     : https://prove2.me/submissions/4bfadc11-243e-4bf3-8a71-9fddb4aa0592

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
variable [DecidableEq ι]
namespace QEC.Semantics.FiniteKrausFamily
theorem _root_.solution
    (U : Matrix.unitaryGroup ι Complex) (i j : ι) :
    (∑ a : ι,
      star ((U : Matrix ι ι Complex) i a) *
        (U : Matrix ι ι Complex) j a) =
      if i = j then 1 else 0 := by
  classical
  have h := congrArg (fun M : Matrix ι ι Complex => M j i)
    (Unitary.coe_mul_star_self U)
  have hsum :
      (∑ a : ι,
        (U : Matrix ι ι Complex) j a *
          star ((U : Matrix ι ι Complex) i a)) =
        if j = i then 1 else 0 := by
    simpa [Matrix.mul_apply, Matrix.one_apply] using h
  calc
    (∑ a : ι,
      star ((U : Matrix ι ι Complex) i a) *
        (U : Matrix ι ι Complex) j a)
        = ∑ a : ι,
            (U : Matrix ι ι Complex) j a *
              star ((U : Matrix ι ι Complex) i a) := by
              apply Finset.sum_congr rfl
              intro a _ha
              ring
    _ = if j = i then 1 else 0 := hsum
    _ = if i = j then 1 else 0 := by
      by_cases hij : i = j <;> simp [hij, eq_comm]
end QEC.Semantics.FiniteKrausFamily
