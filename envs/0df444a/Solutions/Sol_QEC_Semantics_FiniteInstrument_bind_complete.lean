-- Prove2me | solution 1 for QEC.Semantics.FiniteInstrument.bind_complete
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:39:02.215407+00:00
-- url     : https://prove2.me/submissions/ba809538-2e24-43e7-a087-dda64b06ef95

import Definitions.Def_QEC_Semantics_Instruments_Core
import Definitions.Def_QEC_Semantics_Instruments_Sequential_Composition
import Theorems.Thm_QEC_Semantics_FiniteInstrument_bind_inducedMap_apply
import Theorems.Thm_QEC_Semantics_FiniteKrausFamily_complete_of_inducedMap_trace_preserving


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
    (hI : I.kraus.Complete)
    (hJ : ∀ outcome, (J outcome).kraus.Complete) :
    (I.bind J).kraus.Complete := by
  apply FiniteKrausFamily.complete_of_inducedMap_trace_preserving
  intro A
  rw [I.bind_inducedMap_apply J A, map_sum]
  calc
    (∑ firstIndex : κ,
        LinearMap.trace Complex L
          ((J (I.observe firstIndex)).kraus.inducedMap
            ((I.kraus.operator firstIndex).comp
              (A.comp (LinearMap.adjoint (I.kraus.operator firstIndex)))))) =
        ∑ firstIndex : κ,
          LinearMap.trace Complex K
            ((I.kraus.operator firstIndex).comp
              (A.comp (LinearMap.adjoint (I.kraus.operator firstIndex)))) := by
          apply Finset.sum_congr rfl
          intro firstIndex _
          exact
            (J (I.observe firstIndex)).kraus.inducedMap_trace_preserving
              (hJ (I.observe firstIndex)) _
    _ = LinearMap.trace Complex K (I.kraus.inducedMap A) := by
          rw [FiniteKrausFamily.inducedMap_apply, map_sum]
    _ = LinearMap.trace Complex H A :=
          I.kraus.inducedMap_trace_preserving hI A
end QEC.Semantics.FiniteInstrument
