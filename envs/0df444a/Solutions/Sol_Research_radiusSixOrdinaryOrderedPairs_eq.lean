-- Prove2me | solution 1 for Research.radiusSixOrdinaryOrderedPairs_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T17:52:54.658061+00:00
-- url     : https://prove2.me/submissions/99996f0f-3148-4664-b4bc-7155f4d22ba2

module
public import Definitions.Def_Research_TriangularShells
public import Definitions.Def_Research_GlobalShellSix

set_option autoImplicit true
@[expose] public section
public section
open Research
set_option maxRecDepth 100000
attribute [local instance] Research.prodLexLinearOrder
namespace Research
theorem _root_.solution {α : Type*} [Fintype α]
    [LinearOrder α] (p : α → ℝ × ℝ) :
    radiusSixOrdinaryOrderedPairs p = radiusSixOrderedPairs p := by
  ext q
  simp only [radiusSixOrdinaryOrderedPairs, radiusSixOrderedPairs,
    Finset.mem_filter]
  constructor
  · rintro ⟨hlt, hd⟩
    refine ⟨hlt, ?_⟩
    rw [Real.sqrt_le_iff] at hd
    norm_num at hd ⊢
    exact hd
  · rintro ⟨hlt, hd⟩
    refine ⟨hlt, ?_⟩
    rw [Real.sqrt_le_iff]
    norm_num at hd ⊢
    exact hd
end Research
