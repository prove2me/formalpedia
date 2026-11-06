-- Prove2me | solution 1 for QEC.Semantics.FiniteKrausFamily.mem_sameSpaceErrorSet_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:20:27.231242+00:00
-- url     : https://prove2.me/submissions/c52e47e6-598e-4106-ac04-000e9b312282

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
theorem _root_.solution (E : FiniteKrausFamily ι H H) (F : Operator H) :
    F ∈ E.sameSpaceErrorSet ↔ ∃ i : ι, E.operator i = F :=
  Iff.rfl
end QEC.Semantics.FiniteKrausFamily
