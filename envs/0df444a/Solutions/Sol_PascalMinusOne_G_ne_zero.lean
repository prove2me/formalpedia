-- Prove2me | solution 1 for PascalMinusOne.G_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:20:27.737332+00:00
-- url     : https://prove2.me/submissions/012c70a7-2280-4753-8078-f12903e30583

import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Definitions.Def_PascalMinusOne_Basic
import Theorems.Thm_PascalMinusOne_m_mem_admissibleIndices

set_option autoImplicit true
open PascalMinusOne
namespace PascalMinusOne
theorem _root_.solution {N m : ℕ} (hm : 0 < m) (hNm : m < N) :
    G N m ≠ 0 := by
  rw [G, Finset.gcd_ne_zero_iff]
  refine ⟨m, m_mem_admissibleIndices hm hNm, ?_⟩
  exact Nat.choose_ne_zero_iff.mpr hNm.le
end PascalMinusOne
