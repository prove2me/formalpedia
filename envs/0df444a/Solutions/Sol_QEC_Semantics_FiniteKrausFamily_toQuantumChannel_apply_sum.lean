-- Prove2me | solution 1 for QEC.Semantics.FiniteKrausFamily.toQuantumChannel_apply_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:18:18.235896+00:00
-- url     : https://prove2.me/submissions/f7c8f6f6-49a9-4ff5-b9bf-ed799ce52791

import Definitions.Def_QEC_Semantics_Channels_Core
import Definitions.Def_QEC_Semantics_Channels_Kraus

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
theorem _root_.solution (E : FiniteKrausFamily ι H K) (hE : E.Complete)
    (A : Operator H) :
    (E.toQuantumChannel hE) A =
      ∑ i : ι, (E.operator i).comp (A.comp (LinearMap.adjoint (E.operator i))) := by
  rw [toQuantumChannel_apply, inducedMap_apply]
end QEC.Semantics.FiniteKrausFamily
