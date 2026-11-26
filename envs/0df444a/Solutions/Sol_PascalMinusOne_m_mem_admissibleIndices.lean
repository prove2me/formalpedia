-- Prove2me | solution 1 for PascalMinusOne.m_mem_admissibleIndices
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:19:50.725643+00:00
-- url     : https://prove2.me/submissions/98baaf33-0ad0-4558-8971-1aa677202887

import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Definitions.Def_PascalMinusOne_Basic
import Theorems.Thm_PascalMinusOne_mem_admissibleIndices_iff
attribute [local simp] PascalMinusOne.mem_admissibleIndices_iff

set_option autoImplicit true
open PascalMinusOne
namespace PascalMinusOne
theorem _root_.solution {N m : ℕ} (hm : 0 < m) (hmN : m < N) :
    m ∈ admissibleIndices N m := by
  simp [admissibleIndices, hm, hmN]
end PascalMinusOne
