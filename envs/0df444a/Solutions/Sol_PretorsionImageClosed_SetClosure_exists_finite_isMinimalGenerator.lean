-- Prove2me | solution 1 for PretorsionImageClosed.SetClosure.exists_finite_isMinimalGenerator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T06:28:18.791286+00:00
-- url     : https://prove2.me/submissions/be939e6c-a15e-459b-b6d4-3ce38675da74

module
public import Mathlib.Order.CompactlyGenerated.Basic
public import Definitions.Def_PretorsionImageClosed_ConvexGeometry_CompletelyJoinIrreducible
public import Definitions.Def_PretorsionImageClosed_ConvexGeometry_Compact

set_option autoImplicit true
@[expose] public section
public section
open Set
open PretorsionImageClosed PretorsionImageClosed.SetClosure
variable {E : Type*} {c : SetClosure E}
namespace PretorsionImageClosed.SetClosure
theorem _root_.solution
    {B C : Set E} (hBfin : B.Finite) (hBC : c B = C) :
    ∃ B₀ : Set E, B₀.Finite ∧ B₀ ⊆ B ∧ c.IsMinimalGenerator B₀ C := by
  let P : Set (Set E) := {B₀ | B₀ ⊆ B ∧ c B₀ = C}
  have hPfin : P.Finite := by
    apply hBfin.powerset.subset
    intro B₀ hB₀
    exact hB₀.1
  have hPnonempty : P.Nonempty := ⟨B, subset_rfl, hBC⟩
  obtain ⟨B₀, hB₀min⟩ := hPfin.exists_minimal hPnonempty
  have hB₀fin : B₀.Finite :=
    hBfin.subset hB₀min.prop.1
  refine ⟨B₀, hB₀fin, hB₀min.prop.1, hB₀min.prop.2, ?_⟩
  intro b hb hdel
  have hproper : B₀ \ {b} ⊂ B₀ := by
    rw [Set.ssubset_iff_subset_ne]
    refine ⟨sdiff_subset, ?_⟩
    intro heq
    have : b ∈ B₀ \ {b} := heq.symm ▸ hb
    exact this.2 rfl
  apply hB₀min.not_prop_of_ssubset hproper
  exact ⟨sdiff_subset.trans hB₀min.prop.1, hdel⟩
end PretorsionImageClosed.SetClosure
