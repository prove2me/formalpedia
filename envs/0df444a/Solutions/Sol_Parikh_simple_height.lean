-- Prove2me | solution 1 for Parikh.simple_height
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T09:49:57.583124+00:00
-- url     : https://prove2.me/submissions/2efdc05f-fc2c-463b-8b65-1c7e960e0169

module
public import Definitions.Def_LeanPool_Parikh_GrammarTrees
public import Definitions.Def_LeanPool_Parikh_BoundedCutSupport
public import Definitions.Def_LeanPool_Parikh_ParseTreePaths
public import Definitions.Def_LeanPool_Parikh_TreePlugging
public import Definitions.Def_LeanPool_Parikh_TreeReplacement
public import Mathlib.Algebra.Order.Group.Nat
public import Definitions.Def_LeanPool_Parikh_Decomposition
public import Theorems.Thm_Parikh_ParseTree_exists_labelPath_height
public import Theorems.Thm_Parikh_ParseTree_labelPath_subset_support
public import Theorems.Thm_Parikh_complete_support_active


set_option autoImplicit true
@[expose] public section
public section
open Parikh
variable {T : Type*}
namespace Parikh
theorem _root_.solution (g : ContextFreeGrammar T) (t : ParseTree T g.NT)
    (ht : Complete g t) (hs : t.Simple) :
    t.height ≤ (activeNonterminals g).card := by
  classical
  obtain ⟨path, hp, hlen⟩ := t.exists_labelPath_height
  have hsubset : path.toFinset ⊆ activeNonterminals g := by
    intro A hA
    exact complete_support_active g t ht
      (t.labelPath_subset_support path hp A (List.mem_toFinset.mp hA))
  rw [← hlen, ← List.toFinset_card_of_nodup (hs path hp)]
  exact Finset.card_le_card hsubset
end Parikh
