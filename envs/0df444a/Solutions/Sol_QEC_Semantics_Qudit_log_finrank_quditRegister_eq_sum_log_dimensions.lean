-- Prove2me | solution 1 for QEC.Semantics.Qudit.log_finrank_quditRegister_eq_sum_log_dimensions
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:14:57.266247+00:00
-- url     : https://prove2.me/submissions/666fbdec-7793-46cb-b512-5ffb9b74193c

import Definitions.Def_QEC_Semantics_Entropy_FiniteDimensional
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditSubsystem
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Definitions.Def_QEC_Semantics_Entropy_QuditBounds
import Theorems.Thm_QEC_Semantics_Qudit_finrank_quditRegister_eq_prod_dimensions
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
open scoped BigOperators ComplexOrder
noncomputable section
open QEC.Semantics.Qudit
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
namespace QEC.Semantics.Qudit
theorem _root_.solution (q : ι -> Nat)
    (hq : forall i, 0 < q i) :
    Real.logb 2 (Module.finrank Complex (QuditRegister q) : Real) =
      ∑ i, Real.logb 2 (q i : Real) := by
  rw [finrank_quditRegister_eq_prod_dimensions]
  push_cast
  simpa using Real.logb_prod Finset.univ (fun i => (q i : Real)) (fun i _ => by
    change (q i : Real) ≠ 0
    exact_mod_cast Nat.ne_of_gt (hq i))
end QEC.Semantics.Qudit
