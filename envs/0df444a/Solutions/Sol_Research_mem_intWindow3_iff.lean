-- Prove2me | solution 1 for Research.mem_intWindow3_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T17:48:30.294305+00:00
-- url     : https://prove2.me/submissions/6db3d6de-7203-43a5-89d5-6f1dc592e5ad

module
public import Definitions.Def_Research_Basic
public import Definitions.Def_Research_TriangularShells

set_option autoImplicit true
@[expose] public section
public section
open Research
namespace Research
theorem _root_.solution (z : ℤ) :
    z ∈ intWindow3 ↔ -3 ≤ z ∧ z ≤ 3 := by
  simp [intWindow3]
  omega
end Research
