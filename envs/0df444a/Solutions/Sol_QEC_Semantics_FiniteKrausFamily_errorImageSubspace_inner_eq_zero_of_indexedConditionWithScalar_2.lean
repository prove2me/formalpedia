-- Prove2me | solution 2 for QEC.Semantics.FiniteKrausFamily.errorImageSubspace_inner_eq_zero_of_indexedConditionWithScalar
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:43:38.493435+00:00
-- url     : https://prove2.me/submissions/25611c8f-90dd-4bea-8ea3-e5a4f19949f7

import Definitions.Def_QEC_Semantics_Channels_Kraus
import Definitions.Def_QEC_Semantics_ErrorCorrection_KnillLaflamme
import Definitions.Def_QEC_Semantics_Channels_KrausKnillLaflamme
import Theorems.Thm_QEC_Semantics_FiniteKrausFamily_mem_errorImageSubspace_iff

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
    {scalar : ι → ι → Complex}
    (h : IndexedKnillLaflammeConditionWithScalar E C scalar)
    {i j : ι} (hzero : scalar i j = 0) :
    ∀ x : H, x ∈ E.errorImageSubspace C i →
      ∀ y : H, y ∈ E.errorImageSubspace C j →
        inner Complex x y = 0 := by
  intro x hx y hy
  rcases (E.mem_errorImageSubspace_iff C i x).1 hx with ⟨x₀, hx₀, hxmap⟩
  rcases (E.mem_errorImageSubspace_iff C j y).1 hy with ⟨y₀, hy₀, hymap⟩
  rw [← hxmap, ← hymap]
  calc
    inner Complex (E.operator i x₀) (E.operator j y₀)
        = scalar i j * inner Complex x₀ y₀ := h i j x₀ hx₀ y₀ hy₀
    _ = 0 := by rw [hzero, zero_mul]
end QEC.Semantics.FiniteKrausFamily
