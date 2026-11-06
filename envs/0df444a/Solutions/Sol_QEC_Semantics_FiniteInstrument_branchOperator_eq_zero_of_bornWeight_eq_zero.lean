-- Prove2me | solution 1 for QEC.Semantics.FiniteInstrument.branchOperator_eq_zero_of_bornWeight_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:36:05.423646+00:00
-- url     : https://prove2.me/submissions/a80cb732-7629-4d9b-ac7e-8dc5daa11518

import Definitions.Def_QEC_Semantics_Channels_Kraus
import Definitions.Def_QEC_Semantics_Instruments_Core
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Semantics.QuantumChannel.comp_apply
attribute [local simp] QEC.Semantics.QuantumChannel.id_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator


section
universe u v w
namespace QEC
namespace Semantics
open scoped BigOperators ComplexOrder
noncomputable section
namespace FiniteInstrument
variable {κ : Type v} [Fintype κ]
variable {Ω : Type w} [Fintype Ω]
variable {H K : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
variable [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
private theorem positiveOperator_eq_zero_of_trace_eq_zero
    {A : Operator K} (hA : LinearMap.IsPositive A)
    (htrace : LinearMap.trace Complex K A = 0) :
    A = 0 := by
  classical
  let b := stdOrthonormalBasis Complex K
  have hmatrix :
      (LinearMap.toMatrix b.toBasis b.toBasis A).PosSemidef :=
    (LinearMap.posSemidef_toMatrix_iff b).2 hA
  have hmatrixTrace :
      Matrix.trace (LinearMap.toMatrix b.toBasis b.toBasis A) = 0 := by
    rw [← LinearMap.trace_eq_matrix_trace Complex b.toBasis]
    exact htrace
  apply (LinearMap.toMatrix b.toBasis b.toBasis).injective
  simpa using (hmatrix.trace_eq_zero_iff).1 hmatrixTrace
end FiniteInstrument
end
end Semantics
end QEC
end

set_option autoImplicit false
universe u v w
open QEC
open QEC.Semantics
open scoped BigOperators ComplexOrder
noncomputable section
open QEC.Semantics.FiniteInstrument
variable {κ : Type v} [Fintype κ]
variable {Ω : Type w} [Fintype Ω]
variable {H K : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
variable [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
attribute [local instance] QEC.Semantics.FiniteInstrument._p2m_local_instance_a5f1a79248_39
namespace QEC.Semantics.FiniteInstrument
theorem _root_.solution
    (I : FiniteInstrument κ Ω H K) (outcome : Ω)
    (rho : DensityOperator H) (hzero : I.bornWeight outcome rho = 0) :
    I.branchOperator outcome rho.toOperator = 0 := by
  apply positiveOperator_eq_zero_of_trace_eq_zero
    (I.branchOperator_positive outcome rho.positive)
  rw [I.trace_branchOperator_eq_bornWeight outcome rho, hzero]
  norm_num
end QEC.Semantics.FiniteInstrument
