-- Prove2me | solution 1 for QEC.Semantics.FiniteKrausFamily.indexedConditionWithScalar_of_matrixConditionWithScalar
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:33:06.489322+00:00
-- url     : https://prove2.me/submissions/a7c440fd-eda6-4842-bdd0-475a990cc63b

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
    {E : FiniteKrausFamily ι H H} {C : QuantumCode H}
    {scalar : Operator H → Operator H → Complex}
    (h : KnillLaflammeMatrixConditionWithScalar C E.sameSpaceErrorSet scalar) :
    IndexedKnillLaflammeConditionWithScalar E C
      (fun i j => scalar (E.operator i) (E.operator j)) := by
  intro i j x hx y hy
  exact h (by exact ⟨i, rfl⟩) (by exact ⟨j, rfl⟩) x hx y hy
end QEC.Semantics.FiniteKrausFamily
