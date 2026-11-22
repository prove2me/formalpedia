-- Prove2me | solution 1 for Parikh.bounded_cut
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T09:50:36.032053+00:00
-- url     : https://prove2.me/submissions/6849b81a-4ccc-414b-b202-35b76b3d1287

module
public import Definitions.Def_LeanPool_Parikh_GrammarTrees
public import Definitions.Def_LeanPool_Parikh_BoundedCutSupport
public import Definitions.Def_LeanPool_Parikh_ParseTreePaths
public import Definitions.Def_LeanPool_Parikh_TreePlugging
public import Definitions.Def_LeanPool_Parikh_TreeReplacement
public import Mathlib.Algebra.Order.Group.Nat
public import Definitions.Def_LeanPool_Parikh_Decomposition
public import Theorems.Thm_Parikh_simple_height
public import Theorems.Thm_Parikh_Complete_exists_minimal_nonsimple_subtree
public import Theorems.Thm_Parikh_Complete_mem_support_iff_subtree
public import Theorems.Thm_Parikh_Complete_subtree_context
public import Theorems.Thm_Parikh_ParseTree_exists_root_mem_child_support
public import Theorems.Thm_Parikh_ParseTree_height_le_height_plug
public import Theorems.Thm_Parikh_ParseTree_productionSize_plug
public import Theorems.Thm_Parikh_ParseTree_productionSize_subtree_bound
public import Theorems.Thm_Parikh_ParseTree_subtree_replacement
public import Theorems.Thm_Parikh_Valid_plug_complete


set_option autoImplicit true
@[expose] public section
public section
open Parikh
variable {T : Type*}
namespace Parikh
theorem _root_.solution (g : ContextFreeGrammar T) (t : ParseTree T g.NT)
    (ht : Complete g t) (hs : ¬ t.Simple) :
    ∃ smaller C, Complete g smaller ∧ smaller.root = t.root ∧
      IsBoundedCycle g C ∧ Inserts g smaller C t ∧
      smaller.productionSize < t.productionSize := by
  classical
  -- Descend to a non-simple occurrence whose side branches are all simple.
  obtain ⟨q, r, cs, hpos, hU, hsU, hsimple⟩ :=
    ht.exists_minimal_nonsimple_subtree hs
  let U : ParseTree T g.NT := .node r cs
  have hchildren : ∀ c ∈ cs, Complete g c := by
    obtain ⟨hv, hh⟩ := hU
    cases hv with
    | node _ _ hr hc roots =>
      have hholes : ∀ c ∈ cs, c.holes = [] := by
        simpa only [ParseTree.holes, List.flatten_eq_nil_iff, List.forall_mem_map] using hh
      exact fun c hc' => ⟨hc c hc', hholes c hc'⟩
  have hheight : U.height ≤ (activeNonterminals g).card + 1 := by
    have hchildheight : ∀ c ∈ cs, c.height ≤ (activeNonterminals g).card :=
      fun c hc => simple_height g c (hchildren c hc) (hsimple c hc)
    have hfold : (cs.map ParseTree.height).foldl max 0 ≤ (activeNonterminals g).card := by
      by_cases hcs : cs = []
      · simp [hcs]
      · have hne : cs.map ParseTree.height ≠ [] := fun h => hcs (List.map_eq_nil_iff.mp h)
        rw [List.foldl_max_eq_max hne, Nat.zero_max]
        apply (List.max_le_iff hne).mpr
        intro n hn
        obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hn
        exact hchildheight c hc
    simpa only [U, ParseTree.height, Nat.add_comm] using Nat.add_le_add_left hfold 1
  -- The repeated root gives a proper descendant with the same root symbol.
  obtain ⟨c, hcmem, hrootmem⟩ :=
    ParseTree.exists_root_mem_child_support r cs hsU hsimple
  obtain ⟨p, v, hp, hvroot⟩ := ((hchildren c hcmem).mem_support_iff_subtree r.input).mp hrootmem
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hcmem
  have hvpos : U.subtree (i :: p) = some v := by simp [U, ParseTree.subtree, hi, hp]
  obtain ⟨hv, C, hC, hCroot, hCplug, _⟩ := hU.subtree_context (i :: p) v hvpos r.input hvroot
  have hvsize : v.productionSize < U.productionSize :=
    (U.productionSize_subtree_bound (i :: p) v hvpos).2 (by simp)
  dsimp only [U] at hvsize
  have hCsize : 0 < C.productionSize := by
    have hsize := C.productionSize_plug v
    rw [hC.2, List.length_singleton, Nat.one_mul, hCplug] at hsize
    omega
  have hcycle : Cycle g C r.input := ⟨hC, hCroot, hCsize⟩
  have hCheight : C.height ≤ (activeNonterminals g).card + 1 := by
    have hle := C.height_le_height_plug v
    rw [hCplug] at hle
    exact hle.trans hheight
  -- Replace U by the descendant v; round-trip replacement certifies reconstruction.
  obtain ⟨_, E, hE, hEroot, hEplug, hreplace⟩ :=
    ht.subtree_context q U hpos r.input rfl
  have hsmall := hE.1.plug_complete hv (by
    intro A hA
    have heq : A = r.input := by simpa only [hE.2, List.mem_singleton] using hA
    simpa only [heq] using hvroot)
  obtain ⟨smaller, hreplace', hsub, hundo⟩ := t.subtree_replacement q U v hpos
  have heq : smaller = E.plug v := Option.some.inj (hreplace'.symm.trans (hreplace v))
  subst smaller
  refine ⟨E.plug v, C, hsmall.1, hsmall.2.trans hEroot, ⟨⟨r.input, hcycle⟩, hCheight⟩,
    ⟨hsmall.1, ht, r.input, hcycle, q, v, hsub, hvroot, ?_⟩, ?_⟩
  · rw [hCplug]
    exact hundo
  · have hbefore := E.productionSize_plug U
    have hafter := E.productionSize_plug v
    dsimp only [U] at hbefore
    simp only [hE.2, List.length_singleton, Nat.one_mul] at hbefore hafter
    rw [hEplug] at hbefore
    omega
end Parikh
