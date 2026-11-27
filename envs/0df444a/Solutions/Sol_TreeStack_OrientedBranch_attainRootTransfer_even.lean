-- Prove2me | solution 1 for TreeStack.OrientedBranch.attainRootTransfer_even
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:37:14.031193+00:00
-- url     : https://prove2.me/submissions/b578f28a-ee83-41f8-8e34-1e4c7eedcc27

import Mathlib
import Definitions.Def_TreeStack_PebblingMove
import Definitions.Def_TreeStack_Message
import Definitions.Def_TreeStack_Boundary
import Theorems.Thm_TreeStack_OrientedBranch_root_mem_carrier
import Theorems.Thm_TreeStack_OrientedBranch_parent_mem_carrier
import Theorems.Thm_TreeStack_OrientedBranch_BranchReach_repeat_move
import Theorems.Thm_TreeStack_F_eq_nonneg_iff
import Theorems.Thm_TreeStack_F_three
import Theorems.Thm_TreeStack_F_two
import Theorems.Thm_TreeStack_OrientedBranch_childBranch_parent
import Theorems.Thm_TreeStack_OrientedBranch_childBranch_root
import Theorems.Thm_TreeStack_OrientedBranch_messageContribution_empty
import Theorems.Thm_TreeStack_OrientedBranch_messageContribution_some
import Theorems.Thm_TreeStack_OrientedBranch_parent_not_mem_vertices
import Theorems.Thm_TreeStack_OrientedBranch_root_mem_vertices
import Theorems.Thm_TreeStack_OrientedBranch_root_ne_parent
import Theorems.Thm_TreeStack_empty_ne_integer_zero
import Theorems.Thm_TreeStack_mass_oneOn
import Theorems.Thm_TreeStack_mem_support_iff
import Theorems.Thm_TreeStack_oneOn_apply
attribute [local simp] TreeStack.F_three
attribute [local simp] TreeStack.F_two
attribute [local simp] TreeStack.OrientedBranch.childBranch_parent
attribute [local simp] TreeStack.OrientedBranch.childBranch_root
attribute [local simp] TreeStack.OrientedBranch.messageContribution_empty
attribute [local simp] TreeStack.OrientedBranch.messageContribution_some
attribute [local simp] TreeStack.OrientedBranch.root_mem_vertices
attribute [local simp] TreeStack.OrientedBranch.root_ne_parent
attribute [local simp] TreeStack.empty_ne_integer_zero
attribute [local simp] TreeStack.mass_oneOn
attribute [local simp] TreeStack.mem_support_iff
attribute [local simp] TreeStack.oneOn_apply


attribute [local simp] TreeStack.OrientedBranch.root_mem_carrier
attribute [local simp] TreeStack.OrientedBranch.parent_mem_carrier

set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}
variable [DecidableEq V]
namespace TreeStack.OrientedBranch
theorem _root_.solution
    (B : OrientedBranch T) (E : Configuration V) (k : ℕ)
    (hk : 1 ≤ k)
    (hRoot : E B.root = 2 * k)
    (hNonroot :
      ∀ v ∈ B.vertices, v ≠ B.root → E v = 0) :
    ∃ D : Configuration V,
      B.BranchReach E D ∧
      B.Cleared D ∧
      (D B.parent : ℤ) =
        (E B.parent : ℤ) + F (E B.root : ℤ) := by
  classical
  have hEnough : 2 * k ≤ E B.root := by
    omega
  rcases BranchReach.repeat_move B B.adj
      B.root_mem_carrier B.parent_mem_carrier E k hEnough with
    ⟨D, hReach, hDroot, hDparent, hOther⟩
  have hRootZero : D B.root = 0 := by
    rw [hDroot, hRoot]
    omega
  have hCleared : B.Cleared D := by
    intro v hv
    by_cases hvr : v = B.root
    · subst v
      exact hRootZero
    · have hvp : v ≠ B.parent := by
        intro hvp
        subst v
        exact B.parent_not_mem_vertices hv
      rw [hOther v hvr hvp]
      exact hNonroot v hv hvr
  have hkZ : 0 ≤ (k : ℤ) := by positivity
  have hkPosZ : 0 < (k : ℤ) := by exact_mod_cast hk
  have hRootZ : (E B.root : ℤ) = 2 * (k : ℤ) := by
    exact_mod_cast hRoot
  have hF : F (E B.root : ℤ) = (k : ℤ) := by
    apply (F_eq_nonneg_iff (z := (E B.root : ℤ))
      (k := (k : ℤ)) hkZ).2
    exact Or.inl ⟨hkPosZ, hRootZ⟩
  have hParentZ :
      (D B.parent : ℤ) =
        (E B.parent : ℤ) + (k : ℤ) := by
    exact_mod_cast hDparent
  refine ⟨D, hReach, hCleared, ?_⟩
  rw [hF]
  exact hParentZ
end TreeStack.OrientedBranch
