-- Prove2me | solution 1 for QEC.Semantics.FiniteKrausFamily.mem_errorImageSubspace_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:32:54.621194+00:00
-- url     : https://prove2.me/submissions/ab6b2d80-bcb4-4d5a-bc46-ac015485c8f1

import Definitions.Def_QEC_Semantics_Channels_Kraus
import Definitions.Def_QEC_Semantics_ErrorCorrection_KnillLaflamme
import Definitions.Def_QEC_Semantics_Channels_KrausKnillLaflamme

set_option autoImplicit false
universe u v
open QEC
open QEC.Semantics
noncomputable section
open QEC.Semantics.FiniteKrausFamily
variable {ι : Type v} [Fintype ι]
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H]
namespace QEC.Semantics.FiniteKrausFamily
theorem _root_.solution
    (E : FiniteKrausFamily ι H H) (C : QuantumCode H) (i : ι) (x : H) :
    x ∈ E.errorImageSubspace C i ↔
      ∃ y : H, y ∈ C.carrier ∧ E.operator i y = x := by
  rfl
end QEC.Semantics.FiniteKrausFamily
