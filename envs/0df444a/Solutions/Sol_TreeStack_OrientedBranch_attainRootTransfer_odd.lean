-- Prove2me | solution 1 for TreeStack.OrientedBranch.attainRootTransfer_odd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:37:43.458043+00:00
-- url     : https://prove2.me/submissions/0111cee3-fd4d-491f-a10a-0fb58a8e9f0d

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
    (hRoot : E B.root = 2 * k + 1)
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
  have hkMinus : 0 ≤ (k : ℤ) - 1 := by
    omega
  have hRootZ :
      (E B.root : ℤ) = 2 * (k : ℤ) + 1 := by
    exact_mod_cast hRoot
  have hF :
      F (E B.root : ℤ) = (k : ℤ) - 1 := by
    apply (F_eq_nonneg_iff (z := (E B.root : ℤ))
      (k := (k : ℤ) - 1) hkMinus).2
    exact Or.inr (by
      rw [hRootZ]
      ring)
  by_cases hq : E B.parent = 0
  · have hk2 : 2 ≤ k := by
      rw [hF, hq] at hPos
      norm_num at hPos
      omega
    have hEnough1 : 2 * 2 ≤ E B.root := by
      rw [hRoot]
      omega
    rcases BranchReach.repeat_move B B.adj
        B.root_mem_carrier B.parent_mem_carrier E 2 hEnough1 with
      ⟨E₁, hReach₁, h1root, h1parent, h1other⟩
    have hEnough2 : 2 * 1 ≤ E₁ B.parent := by
      omega
    rcases BranchReach.repeat_move B B.adj.symm
        B.parent_mem_carrier B.root_mem_carrier E₁ 1 hEnough2 with
      ⟨E₂, hReach₂, h2parent, h2root, h2other⟩
    have hEnough3 : 2 * (k - 1) ≤ E₂ B.root := by
      rw [h2root, h1root, hRoot]
      omega
    rcases BranchReach.repeat_move B B.adj
        B.root_mem_carrier B.parent_mem_carrier E₂ (k - 1) hEnough3 with
      ⟨D, hReach₃, h3root, h3parent, h3other⟩
    have hReach :
        B.BranchReach E D :=
      Relation.ReflTransGen.trans hReach₁
        (Relation.ReflTransGen.trans hReach₂ hReach₃)
    have hRootZero : D B.root = 0 := by
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
        calc
          D v = E₂ v := h3other v hvr hvp
          _ = E₁ v := h2other v hvp hvr
          _ = E v := h1other v hvr hvp
          _ = 0 := hNonroot v hv hvr
    have hParentNat :
        D B.parent = E B.parent + (k - 1) := by
      omega
    have hParentZ :
        (D B.parent : ℤ) =
          (E B.parent : ℤ) + ((k : ℤ) - 1) := by
      calc
        (D B.parent : ℤ) =
            ((E B.parent + (k - 1) : ℕ) : ℤ) := by
              exact_mod_cast hParentNat
        _ = (E B.parent : ℤ) + ((k : ℤ) - 1) := by
              rw [Nat.cast_add, Nat.cast_sub hk]
              norm_num

    refine ⟨D, hReach, hCleared, ?_⟩
    rw [hF]
    exact hParentZ
  · have hq1 : 1 ≤ E B.parent := Nat.one_le_iff_ne_zero.mpr hq
    have hEnough1 : 2 * 1 ≤ E B.root := by
      rw [hRoot]
      omega
    rcases BranchReach.repeat_move B B.adj
        B.root_mem_carrier B.parent_mem_carrier E 1 hEnough1 with
      ⟨E₁, hReach₁, h1root, h1parent, h1other⟩
    have hEnough2 : 2 * 1 ≤ E₁ B.parent := by
      omega
    rcases BranchReach.repeat_move B B.adj.symm
        B.parent_mem_carrier B.root_mem_carrier E₁ 1 hEnough2 with
      ⟨E₂, hReach₂, h2parent, h2root, h2other⟩
    have hEnough3 : 2 * k ≤ E₂ B.root := by
      rw [h2root, h1root, hRoot]
      omega
    rcases BranchReach.repeat_move B B.adj
        B.root_mem_carrier B.parent_mem_carrier E₂ k hEnough3 with
      ⟨D, hReach₃, h3root, h3parent, h3other⟩
    have hReach :
        B.BranchReach E D :=
      Relation.ReflTransGen.trans hReach₁
        (Relation.ReflTransGen.trans hReach₂ hReach₃)
    have hRootZero : D B.root = 0 := by
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
        calc
          D v = E₂ v := h3other v hvr hvp
          _ = E₁ v := h2other v hvp hvr
          _ = E v := h1other v hvr hvp
          _ = 0 := hNonroot v hv hvr
    have hParentNat :
        D B.parent = E B.parent + (k - 1) := by
      omega
    have hParentZ :
        (D B.parent : ℤ) =
          (E B.parent : ℤ) + ((k : ℤ) - 1) := by
      calc
        (D B.parent : ℤ) =
            ((E B.parent + (k - 1) : ℕ) : ℤ) := by
              exact_mod_cast hParentNat
        _ = (E B.parent : ℤ) + ((k : ℤ) - 1) := by
              rw [Nat.cast_add, Nat.cast_sub hk]
              norm_num
    refine ⟨D, hReach, hCleared, ?_⟩
    rw [hF]
    exact hParentZ
end TreeStack.OrientedBranch
