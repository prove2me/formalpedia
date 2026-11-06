-- Prove2me | solution 1 for QEC.Semantics.FiniteInstrument.sum_branchOperator_eq_mapDensity_toOperator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:17:15.384569+00:00
-- url     : https://prove2.me/submissions/a362aa81-fb96-4f01-871c-2086cc8af297

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
theorem _root_.solution
    (I : FiniteInstrument κ Ω H K) (hComplete : I.kraus.Complete)
    (rho : DensityOperator H) :
    ∑ outcome : Ω, I.branchOperator outcome rho.toOperator =
      ((I.kraus.toQuantumChannel hComplete).mapDensity rho).toOperator := by
  rw [I.sum_branchOperator_eq_inducedMap]
  rfl
end QEC.Semantics.FiniteInstrument
