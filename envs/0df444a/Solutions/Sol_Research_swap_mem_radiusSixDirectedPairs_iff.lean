-- Prove2me | solution 1 for Research.swap_mem_radiusSixDirectedPairs_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:09:01.307412+00:00
-- url     : https://prove2.me/submissions/32fa69f0-e7ad-4856-9362-2e0025026d7b

module
public import Definitions.Def_Research_TriangularShells
public import Definitions.Def_Research_GlobalShellSix
public import Theorems.Thm_Research_mem_radiusSixDirectedPairs_iff
public import Theorems.Thm_Research_sqDist_symm

set_option autoImplicit true
@[expose] public section
public section
open Research
set_option maxRecDepth 100000
attribute [local instance] Research.prodLexLinearOrder
namespace Research
theorem _root_.solution {α : Type*} [Fintype α]
    [DecidableEq α] (p : α → ℝ × ℝ) (q : α × α) :
    q.swap ∈ radiusSixDirectedPairs p ↔ q ∈ radiusSixDirectedPairs p := by
  rw [mem_radiusSixDirectedPairs_iff, mem_radiusSixDirectedPairs_iff]
  rcases q with ⟨a, b⟩
  simp only [Prod.swap_prod_mk]
  constructor
  · rintro ⟨hne, hd⟩
    exact ⟨hne.symm, by rwa [sqDist_symm]⟩
  · rintro ⟨hne, hd⟩
    exact ⟨hne.symm, by rwa [sqDist_symm]⟩
end Research
