-- Prove2me | solution 1 for QEC.Semantics.FiniteKrausFamily.errorImageSubspace_inner_eq_zero_of_indexedConditionWithScalar
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-05T17:55:06.082172+00:00
-- url     : https://prove2.me/submissions/cde79a3a-0998-4ba8-b390-114fe7cf3a9d

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

theorem solution {E : FiniteKrausFamily ι H H} {C : QuantumCode H}
    {scalar : ι → ι → Complex}
    (h : IndexedKnillLaflammeConditionWithScalar E C scalar)
    {i j : ι} (hzero : scalar i j = 0) :
    ∀ x : H, x ∈ E.errorImageSubspace C i →
      ∀ y : H, y ∈ E.errorImageSubspace C j →
        inner Complex x y = 0 := by
  solve | rfl | simp [FiniteKrausFamily, IndexedKnillLaflammeConditionWithScalar, errorImageSubspace] | simp_all [FiniteKrausFamily, IndexedKnillLaflammeConditionWithScalar, errorImageSubspace] | omega | norm_num
