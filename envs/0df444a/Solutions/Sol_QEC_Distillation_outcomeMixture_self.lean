-- Prove2me | solution 1 for QEC.Distillation.outcomeMixture_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:15:49.731867+00:00
-- url     : https://prove2.me/submissions/7070a495-e9fc-4814-8fc6-72502f5d9f62

import Definitions.Def_QEC_Semantics_Channels_Core
import Definitions.Def_QEC_Semantics_Entropy_Convexity
import Definitions.Def_QEC_Distillation_Core_MagicStateProtocol
import Theorems.Thm_QEC_Semantics_DensityOperator_convexCombination_toOperator
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Semantics.DensityOperator.convexCombination_toOperator
attribute [local simp] QEC.Semantics.QuantumChannel.comp_apply
attribute [local simp] QEC.Semantics.QuantumChannel.id_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator



set_option autoImplicit false
universe u
open QEC
open QEC.Distillation
open Semantics
open scoped BigOperators
namespace QEC.Distillation
theorem _root_.solution {Output : Type u}
    [NormedAddCommGroup Output] [InnerProductSpace Complex Output]
    [FiniteQuantumSystem Output]
    (successProbability : ℝ) (h0 : 0 ≤ successProbability)
    (h1 : successProbability ≤ 1) (rho : DensityOperator Output) :
    outcomeMixture successProbability h0 h1 rho rho = rho := by
  apply densityOperator_ext
  simp [outcomeMixture, DensityOperator.convexCombinationOperator,
    branchState, outcomeWeight,
    show (Finset.univ : Finset DistillationOutcome) =
      {DistillationOutcome.accepted, DistillationOutcome.rejected} by decide]
end QEC.Distillation
