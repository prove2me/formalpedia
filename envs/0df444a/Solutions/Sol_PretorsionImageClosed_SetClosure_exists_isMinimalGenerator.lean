-- Prove2me | solution 1 for PretorsionImageClosed.SetClosure.exists_isMinimalGenerator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T05:29:50.428725+00:00
-- url     : https://prove2.me/submissions/8b917a57-ff5a-444a-bc19-06ceba40ba05

module
public import Mathlib.Data.Set.Card
public import Definitions.Def_PretorsionImageClosed_ConvexGeometry_Basic
public import Definitions.Def_PretorsionImageClosed_ConvexGeometry_Finite

set_option autoImplicit true
@[expose] public section
public section
open Set
open PretorsionImageClosed PretorsionImageClosed.SetClosure
variable {E : Type*} {c : SetClosure E}
namespace PretorsionImageClosed.SetClosure
theorem _root_.solution [Finite E]
    {C : Set E} (hC : c.IsClosed C) :
    ∃ B : Set E, c.IsMinimalGenerator B C := by
  let P : Set (Set E) := {B | c B = C}
  have hPfin : P.Finite := Set.toFinite P
  have hPnonempty : P.Nonempty := ⟨C, hC.closure_eq⟩
  obtain ⟨B, hBmin⟩ := hPfin.exists_minimal hPnonempty
  refine ⟨B, hBmin.prop, ?_⟩
  intro b hb hdel
  have hproper : B \ {b} ⊂ B := by
    rw [Set.ssubset_iff_subset_ne]
    refine ⟨sdiff_subset, ?_⟩
    intro heq
    have : b ∈ B \ {b} := heq.symm ▸ hb
    exact this.2 rfl
  exact hBmin.not_prop_of_ssubset hproper hdel
end PretorsionImageClosed.SetClosure
