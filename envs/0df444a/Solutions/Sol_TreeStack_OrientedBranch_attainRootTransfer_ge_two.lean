-- Prove2me | solution 1 for TreeStack.OrientedBranch.attainRootTransfer_ge_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:39:24.837607+00:00
-- url     : https://prove2.me/submissions/4482a168-ae48-4c47-8cc7-75e134b3a8ce

import Mathlib
import Definitions.Def_TreeStack_PebblingMove
import Definitions.Def_TreeStack_Message
import Definitions.Def_TreeStack_Boundary
import Theorems.Thm_TreeStack_OrientedBranch_attainRootTransfer_even
import Theorems.Thm_TreeStack_OrientedBranch_attainRootTransfer_odd

set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}
variable [DecidableEq V]
namespace TreeStack.OrientedBranch
theorem _root_.solution
    (B : OrientedBranch T) (E : Configuration V)
    (hRootTwo : 2 ≤ E B.root)
    (hNonroot :
      ∀ v ∈ B.vertices, v ≠ B.root → E v = 0)
    (hPos :
      0 < (E B.parent : ℤ) + F (E B.root : ℤ)) :
    ∃ D : Configuration V,
      B.BranchReach E D ∧
      B.Cleared D ∧
      (D B.parent : ℤ) =
        (E B.parent : ℤ) + F (E B.root : ℤ) := by
  classical
  by_cases hEven : Even (E B.root)
  · rcases hEven with ⟨k, hkEq⟩
    have hRoot : E B.root = 2 * k := by
      omega
    have hk : 1 ≤ k := by
      omega
    exact B.attainRootTransfer_even E k hk hRoot hNonroot
  · have hOdd : Odd (E B.root) :=
      Nat.not_even_iff_odd.mp hEven
    rcases hOdd with ⟨k, hkEq⟩
    have hRoot : E B.root = 2 * k + 1 := by
      omega
    have hk : 1 ≤ k := by
      omega
    exact B.attainRootTransfer_odd E k hk hRoot hNonroot hPos
end TreeStack.OrientedBranch
