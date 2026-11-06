-- Prove2me | solution 1 for QEC.Semantics.FiniteInstrument.sum_bornWeight_eq_trace_re
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:36:00.995197+00:00
-- url     : https://prove2.me/submissions/921a7638-de72-4db6-b8eb-45f32e965891

import Definitions.Def_QEC_Semantics_Channels_Kraus
import Definitions.Def_QEC_Semantics_Instruments_Core
import Theorems.Thm_QEC_Semantics_FiniteInstrument_sum_branchOperator_eq_inducedMap

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
theorem _root_.solution (I : FiniteInstrument κ Ω H K)
    (hComplete : I.kraus.Complete) (rho : DensityOperator H) :
    ∑ outcome : Ω, I.bornWeight outcome rho =
      Complex.re (LinearMap.trace Complex H rho.toOperator) := by
  unfold bornWeight
  rw [← Complex.re_sum, ← map_sum, I.sum_branchOperator_eq_inducedMap]
  rw [I.kraus.inducedMap_trace_preserving hComplete]
end QEC.Semantics.FiniteInstrument
