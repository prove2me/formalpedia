-- Prove2me | solution 1 for Research.sqDist_symm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:03:49.8799+00:00
-- url     : https://prove2.me/submissions/45852add-52b8-4bb7-aa40-31dc41f1678c

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
theorem _root_.solution (p q : ℝ × ℝ) : sqDist p q = sqDist q p := by
  simp only [sqDist]
  ring
end Research
