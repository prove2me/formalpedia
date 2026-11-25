-- Prove2me | solution 1 for PretorsionImageClosed.SetClosure.pointClosure_isCompletelyJoinIrreducible
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T06:28:07.057889+00:00
-- url     : https://prove2.me/submissions/66814fc4-d445-4769-a4b6-3f40a146d7fd

module
public import Definitions.Def_PretorsionImageClosed_ConvexGeometry_ClosedSets
public import Definitions.Def_PretorsionImageClosed_ConvexGeometry_CompletelyJoinIrreducible
public import Theorems.Thm_PretorsionImageClosed_SetClosure_isCompletelyJoinIrreducible_of_greatest_lt
public import Theorems.Thm_PretorsionImageClosed_SetClosure_isClosed_pointClosure_sdiff_singleton
public import Theorems.Thm_PretorsionImageClosed_SetClosure_pointClosure_le_iff


set_option autoImplicit true
@[expose] public section
public section
open Set
open PretorsionImageClosed
open PretorsionImageClosed.SetClosure
variable {E : Type*} {c : SetClosure E}
namespace PretorsionImageClosed.SetClosure
theorem _root_.solution
    (hfin : c.IsFinitary) (hae : c.IsAntiExchange)
    (hempty : c.IsClosed ∅) (x : E) :
    IsCompletelyJoinIrreducible (c.pointClosure x) := by
  let Jₛ : c.Closeds :=
    ⟨c ({x} : Set E) \ {x},
      isClosed_pointClosure_sdiff_singleton hfin hae hempty x⟩
  apply isCompletelyJoinIrreducible_of_greatest_lt (jₛ := Jₛ)
  · change c ({x} : Set E) \ {x} ⊂ c ({x} : Set E)
    rw [Set.ssubset_iff_subset_ne]
    refine ⟨sdiff_subset, ?_⟩
    intro heq
    have hxJ : x ∈ c ({x} : Set E) :=
      c.le_closure {x} (mem_singleton x)
    have : x ∈ c ({x} : Set E) \ {x} := heq.symm ▸ hxJ
    exact this.2 rfl
  · intro A hAJ
    change (A : Set E) ⊆ c ({x} : Set E) \ {x}
    intro y hyA
    refine ⟨hAJ.le hyA, ?_⟩
    intro hyx
    have hxA : x ∈ (A : Set E) := hyx ▸ hyA
    have hJA : c.pointClosure x ≤ A :=
      pointClosure_le_iff.2 hxA
    exact hAJ.2 hJA
end PretorsionImageClosed.SetClosure
