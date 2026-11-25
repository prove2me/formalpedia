-- Prove2me | solution 1 for Research.radiusSixOrdinaryDirectedPairs_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T17:52:48.087751+00:00
-- url     : https://prove2.me/submissions/0529fab9-9e2d-49f5-8146-91f35f787c36

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
    [DecidableEq α] (p : α → ℝ × ℝ) :
    radiusSixOrdinaryDirectedPairs p = radiusSixDirectedPairs p := by
  ext q
  simp only [radiusSixOrdinaryDirectedPairs, radiusSixDirectedPairs,
    Finset.mem_filter]
  constructor
  · rintro ⟨hne, hd⟩
    refine ⟨hne, ?_⟩
    rw [Real.sqrt_le_iff] at hd
    norm_num at hd ⊢
    exact hd
  · rintro ⟨hne, hd⟩
    refine ⟨hne, ?_⟩
    rw [Real.sqrt_le_iff]
    norm_num at hd ⊢
    exact hd
end Research
