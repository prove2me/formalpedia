-- Prove2me | solution 1 for PretorsionImageClosed.SetClosure.finiteClosuresBelow_directed_sSup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T06:58:32.466798+00:00
-- url     : https://prove2.me/submissions/061bbec7-c49f-483b-b87a-4d24ba748a79

module
public import Mathlib.Order.CompactlyGenerated.Basic
public import Definitions.Def_PretorsionImageClosed_ConvexGeometry_CompletelyJoinIrreducible
public import Definitions.Def_PretorsionImageClosed_ConvexGeometry_Compact
public import Theorems.Thm_PretorsionImageClosed_SetClosure_finiteClosure_isCompactElement
public import Theorems.Thm_PretorsionImageClosed_SetClosure_iSup_pointClosure


set_option autoImplicit true
@[expose] public section
public section
open Set
open PretorsionImageClosed PretorsionImageClosed.SetClosure
variable {E : Type*} {c : SetClosure E}
namespace PretorsionImageClosed.SetClosure
theorem _root_.solution
    (hfin : c.IsFinitary) (C : c.Closeds) :
    (c.finiteClosuresBelow C).Nonempty ∧
      DirectedOn (· ≤ ·) (c.finiteClosuresBelow C) ∧
      (∀ K ∈ c.finiteClosuresBelow C, IsCompactElement K) ∧
      sSup (c.finiteClosuresBelow C) = C := by
  classical
  constructor
  · refine ⟨c.toCloseds ∅, ∅, Set.finite_empty, empty_subset _, rfl⟩
  constructor
  · rintro K ⟨B, hBfin, hBC, rfl⟩ L ⟨D, hDfin, hDC, rfl⟩
    refine ⟨c.toCloseds (B ∪ D),
      ⟨B ∪ D, hBfin.union hDfin, union_subset hBC hDC, rfl⟩,
      c.monotone subset_union_left, c.monotone subset_union_right⟩
  constructor
  · intro K hK
    obtain ⟨B, hBfin, -, rfl⟩ := hK
    exact finiteClosure_isCompactElement hfin hBfin
  · apply le_antisymm
    · apply sSup_le
      intro K hK
      obtain ⟨B, -, hBC, rfl⟩ := hK
      exact c.closure_min hBC C.2
    · calc
        C = ⨆ x : (C : Set E), c.pointClosure x.1 :=
          (iSup_pointClosure C).symm
        _ ≤ sSup (c.finiteClosuresBelow C) := by
          apply iSup_le
          intro x
          apply le_sSup
          exact ⟨{x.1}, Set.finite_singleton x.1,
            singleton_subset_iff.mpr x.2, rfl⟩
end PretorsionImageClosed.SetClosure
