-- Prove2me | solution 1 for PretorsionImageClosed.SetClosure.exists_finite_generator_of_isCompactElement
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T06:07:22.826031+00:00
-- url     : https://prove2.me/submissions/2b5b7655-ffdb-4f7f-b713-ecad850030a6

module
public import Mathlib.Order.CompactlyGenerated.Basic
public import Definitions.Def_PretorsionImageClosed_ConvexGeometry_CompletelyJoinIrreducible
public import Definitions.Def_PretorsionImageClosed_ConvexGeometry_Compact
public import Theorems.Thm_PretorsionImageClosed_SetClosure_iSup_pointClosure


set_option autoImplicit true
@[expose] public section
public section
open Set
open PretorsionImageClosed PretorsionImageClosed.SetClosure
variable {E : Type*} {c : SetClosure E}
namespace PretorsionImageClosed.SetClosure
theorem _root_.solution
    {C : c.Closeds} (hcompact : IsCompactElement C) :
    ∃ B : Set E, B.Finite ∧ B ⊆ (C : Set E) ∧ c B = (C : Set E) := by
  classical
  have hne : (c.finiteClosuresBelow C).Nonempty :=
    ⟨c.toCloseds ∅, ∅, Set.finite_empty, empty_subset _, rfl⟩
  have hdir : DirectedOn (· ≤ ·) (c.finiteClosuresBelow C) := by
    rintro K ⟨B, hBfin, hBC, rfl⟩ L ⟨D, hDfin, hDC, rfl⟩
    exact ⟨c.toCloseds (B ∪ D), ⟨B ∪ D, hBfin.union hDfin, union_subset hBC hDC, rfl⟩,
      c.monotone subset_union_left, c.monotone subset_union_right⟩
  have hlub : IsLUB (c.finiteClosuresBelow C) C := by
    refine ⟨?_, ?_⟩
    · rintro K ⟨B, -, hBC, rfl⟩
      exact c.closure_min hBC C.2
    · intro U hU
      rw [← iSup_pointClosure C]
      apply iSup_le
      intro x
      exact hU ⟨{x.1}, Set.finite_singleton x.1, singleton_subset_iff.mpr x.2, rfl⟩
  obtain ⟨K, ⟨B, hBfin, hBC, rfl⟩, hCK⟩ := hcompact (c.finiteClosuresBelow C) C hne hdir hlub le_rfl
  let K : c.Closeds := c.toCloseds B
  have hKC : K ≤ C :=
    c.closure_min hBC C.2
  have hKCeq : K = C := le_antisymm hKC hCK
  refine ⟨B, hBfin, hBC, ?_⟩
  exact congrArg Subtype.val hKCeq
end PretorsionImageClosed.SetClosure
