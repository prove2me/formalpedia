-- Prove2me | solution 1 for QEC.Semantics.FiniteKrausFamily.complete_of_inducedMap_trace_preserving
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:27:15.078813+00:00
-- url     : https://prove2.me/submissions/9407051d-d4f6-46d9-96be-89bd6deb7f42

import Definitions.Def_QEC_Semantics_Channels_Core
import Definitions.Def_QEC_Semantics_Channels_Kraus
import Theorems.Thm_QEC_Semantics_operator_ext_of_trace_comp_right_eq

set_option autoImplicit false
universe u v
open QEC
open QEC.Semantics
open scoped BigOperators
noncomputable section
open QEC.Semantics.FiniteKrausFamily
variable {ι : Type v} [Fintype ι]
variable {H K : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
variable [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
namespace QEC.Semantics.FiniteKrausFamily
theorem _root_.solution (E : FiniteKrausFamily ι H K)
    (htrace : ∀ A : Operator H,
      LinearMap.trace Complex K (E.inducedMap A) = LinearMap.trace Complex H A) :
    E.Complete := by
  classical
  unfold Complete
  apply operator_ext_of_trace_comp_right_eq
  intro A
  calc
    LinearMap.trace Complex H
        (A.comp (∑ i : ι, (LinearMap.adjoint (E.operator i)).comp (E.operator i)))
        = LinearMap.trace Complex K (E.inducedMap A) := by
          rw [E.inducedMap_trace_eq_trace_comp_completeSum]
    _ = LinearMap.trace Complex H A := htrace A
    _ = LinearMap.trace Complex H (A.comp (1 : Operator H)) := rfl
end QEC.Semantics.FiniteKrausFamily
