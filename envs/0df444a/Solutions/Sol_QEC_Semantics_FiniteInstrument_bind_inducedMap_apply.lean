-- Prove2me | solution 1 for QEC.Semantics.FiniteInstrument.bind_inducedMap_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:37:20.130309+00:00
-- url     : https://prove2.me/submissions/e4f8979f-5fbd-40db-b6a7-bf25199de58a

import Definitions.Def_QEC_Semantics_Instruments_Core
import Definitions.Def_QEC_Semantics_Instruments_Sequential_Composition
import Theorems.Thm_QEC_Semantics_FiniteInstrument_conditionalDensity_toOperator
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Semantics.FiniteInstrument.conditionalDensity_toOperator
attribute [local simp] QEC.Semantics.QuantumChannel.comp_apply
attribute [local simp] QEC.Semantics.QuantumChannel.id_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator



set_option autoImplicit false
universe u v w x y
open QEC
open QEC.Semantics
open scoped BigOperators ComplexOrder TensorProduct
noncomputable section
open QEC.Semantics.FiniteInstrument
variable {κ : Type v} [Fintype κ]
variable {Ω : Type w} [Fintype Ω]
variable {κ' : Type x} [Fintype κ']
variable {Ξ : Ω → Type y} [∀ outcome, Fintype (Ξ outcome)]
variable {H K L : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
variable [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
variable [NormedAddCommGroup L] [InnerProductSpace Complex L] [FiniteQuantumSystem L]
namespace QEC.Semantics.FiniteInstrument
theorem _root_.solution (I : FiniteInstrument κ Ω H K)
    (J : (outcome : Ω) → FiniteInstrument κ' (Ξ outcome) K L)
    (A : Operator H) :
    (I.bind J).kraus.inducedMap A =
      ∑ firstIndex : κ,
        (J (I.observe firstIndex)).kraus.inducedMap
          ((I.kraus.operator firstIndex).comp
            (A.comp (LinearMap.adjoint (I.kraus.operator firstIndex)))) := by
  ext x
  simp only [FiniteKrausFamily.inducedMap_apply, bind,
    LinearMap.adjoint_comp, LinearMap.comp_apply, LinearMap.sum_apply,
    Fintype.sum_prod_type]
end QEC.Semantics.FiniteInstrument
