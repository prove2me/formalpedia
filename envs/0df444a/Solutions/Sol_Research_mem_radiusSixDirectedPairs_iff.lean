-- Prove2me | solution 1 for Research.mem_radiusSixDirectedPairs_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T17:48:13.49301+00:00
-- url     : https://prove2.me/submissions/662aad64-4b2e-4a13-a800-0a05c5fc8ea0

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
    [DecidableEq α] (p : α → ℝ × ℝ) (q : α × α) :
    q ∈ radiusSixDirectedPairs p ↔
      q.1 ≠ q.2 ∧ sqDist (p q.1) (p q.2) ≤ 36 := by
  simp [radiusSixDirectedPairs]
end Research
