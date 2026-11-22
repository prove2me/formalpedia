-- Prove2me | solution 1 for OrderClosures.treeFunction_child_properties
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:12:09.183094+00:00
-- url     : https://prove2.me/submissions/222a36f4-6d6f-42b3-a752-744eab77e7b4

module
public import Definitions.Def_LeanPool_OrderClosures_WeaklyFatou_Reductions
public import Definitions.Def_LeanPool_OrderClosures_WeaklyFatou_FiniteTree
public import Theorems.Thm_OrderClosures_mem_treeCylinder_child_iff
public import Theorems.Thm_OrderClosures_treeFunction_apply_of_mem
public import Theorems.Thm_OrderClosures_treeFunction_apply_of_notMem

set_option autoImplicit true
@[expose] public section
public section
open OrderClosures
open Set Filter Topology
open scoped NNReal Topology
universe u
namespace OrderClosures
theorem _root_.solution
    (n : ℕ) (t : TreeNode n) (ht : TreeNode.level t < n) :
    (∀ m, treeCylinder n (TreeNode.child t ht m) ⊆ treeCylinder n t ∧
      treeFunction n (TreeNode.child t ht m) ≤ treeFunction n t) ∧
    Monotone (fun m ↦ treeFunction n (TreeNode.child t ht m)) ∧
      IsLUB (Set.range fun m ↦ treeFunction n (TreeNode.child t ht m))
        (treeFunction n t) := by
  have hnonneg : ∀ u : TreeNode n, 0 ≤ treeFunction n u := by
    intro u α
    change 0 ≤ treeFunction n u α
    by_cases hα : α ∈ treeCylinder n u
    · rw [treeFunction_apply_of_mem n u hα]
      norm_num
    · rw [treeFunction_apply_of_notMem n u hα]
  have hindicator_mono : ∀ {u v : TreeNode n},
      treeCylinder n u ⊆ treeCylinder n v → treeFunction n u ≤ treeFunction n v := by
    intro u v huv α
    change treeFunction n u α ≤ treeFunction n v α
    by_cases hα : α ∈ treeCylinder n u
    · rw [treeFunction_apply_of_mem n u hα,
        treeFunction_apply_of_mem n v (huv hα)]
    · rw [treeFunction_apply_of_notMem n u hα]
      exact hnonneg v α
  have hsubset : ∀ m,
      treeCylinder n (TreeNode.child t ht m) ⊆ treeCylinder n t := by
    intro m α hα
    exact (mem_treeCylinder_child_iff n t ht m α).mp hα |>.1
  have hle : ∀ m, treeFunction n (TreeNode.child t ht m) ≤ treeFunction n t :=
    fun m ↦ hindicator_mono (hsubset m)
  refine ⟨fun m ↦ ⟨hsubset m, hle m⟩, ?_, ?_⟩
  · intro a b hab
    apply hindicator_mono
    intro α hα
    rcases (mem_treeCylinder_child_iff n t ht a α).mp hα with ⟨hαt, hlast⟩
    exact (mem_treeCylinder_child_iff n t ht b α).mpr ⟨hαt, hlast.trans hab⟩
  · constructor
    · rintro _ ⟨m, rfl⟩
      exact hle m
    · intro g hg α
      change treeFunction n t α ≤ g α
      by_cases hα : α ∈ treeCylinder n t
      · let m := α ⟨t, ht⟩
        have hchild : α ∈ treeCylinder n (TreeNode.child t ht m) :=
          (mem_treeCylinder_child_iff n t ht m α).mpr ⟨hα, le_rfl⟩
        calc
          treeFunction n t α = 1 := treeFunction_apply_of_mem n t hα
          _ = treeFunction n (TreeNode.child t ht m) α :=
            (treeFunction_apply_of_mem n _ hchild).symm
          _ ≤ g α := hg ⟨m, rfl⟩ α
      · rw [treeFunction_apply_of_notMem n t hα]
        exact (hnonneg (TreeNode.child t ht 0) α).trans (hg ⟨0, rfl⟩ α)
end OrderClosures
