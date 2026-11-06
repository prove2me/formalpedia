-- Prove2me | solution 1 for QEC.Semantics.DensityOperator.inner_eq_sum_reprs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:46:42.714735+00:00
-- url     : https://prove2.me/submissions/eb4f96b3-c67e-400f-847e-ff316700b80e

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
omit [FiniteQuantumSystem H]
namespace QEC.Semantics.DensityOperator
theorem _root_.solution
    (b : OrthonormalBasis (Fin (Module.finrank Complex H)) Complex H) (x y : H) :
    inner Complex x y = ∑ i, star (b.repr x i) * b.repr y i := by
  calc
    inner Complex x y = inner Complex (∑ i, b.repr x i • b i) y :=
      congrArg (fun z => inner Complex z y) (b.sum_repr x).symm
    _ = ∑ i, star (b.repr x i) * b.repr y i := by
      rw [sum_inner]
      simp [inner_smul_left, OrthonormalBasis.repr_apply_apply]
end QEC.Semantics.DensityOperator
