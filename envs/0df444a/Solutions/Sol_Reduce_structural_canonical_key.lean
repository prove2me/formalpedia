-- Prove2me | solution 1 for Reduce.structural_canonical_key
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:06:20.670301+00:00
-- url     : https://prove2.me/submissions/d8e8ea70-726a-4db8-8239-8135eeb51e52

import Definitions.Def_Bdd_Collect
import Mathlib.Data.Sum.Order
import Definitions.Def_Bdd_Reduce_State
import Theorems.Thm_Nary_restrict_const
import Theorems.Thm_OBdd_init_inductionOn
import Theorems.Thm_P2M_OBdd_toTree_terminal__6f80b985dd51
attribute [local simp] Nary.restrict_const



set_option autoImplicit true
attribute [local instance_reducible] OBdd Bdd.Ordered
open Pointer
open Bdd
open RawBdd
open Reduce
namespace Reduce
theorem _root_.solution {n s : Nat} {M : Vector (Node n s) s}
    (node_inj : ∀ (kp kq : Fin s),
        M[kp].var = M[kq].var → M[kp].low = M[kq].low → M[kp].high = M[kq].high → kp = kq) :
    ∀ (P Q : OBdd n s), P.1.heap = M → Q.1.heap = M →
      OBdd.toTree P = OBdd.toTree Q → P.1.root = Q.1.root := by
  intro P
  induction P using OBdd.init_inductionOn with
  | base b =>
    intro Q hP_heap hQ_heap htree_eq
    have htree_eq : DecisionTree.leaf b = OBdd.toTree Q :=
      OBdd.toTree_terminal.symm.trans htree_eq
    cases hQ : Q.1.root with
    | terminal bq =>
      rw [OBdd.toTree_terminal' hQ] at htree_eq
      injection htree_eq with htree_eq
      exact congrArg _ htree_eq
    | node jq =>
      rw [OBdd.toTree_node hQ] at htree_eq
      exact absurd htree_eq (by simp)
  | step jp hl_ord ih_lo hh_ord ih_hi hj_ord =>
    intro Q hP_heap hQ_heap htree_eq
    cases hQ : Q.1.root with
    | terminal bq =>
      rw [OBdd.toTree_node (O := ⟨_, hj_ord⟩) rfl, OBdd.toTree_terminal' hQ] at htree_eq
      exact absurd htree_eq (by simp)
    | node jq =>
      have hQ_ord : Bdd.Ordered ⟨Q.1.heap, Pointer.node jq⟩ := by
        rcases Q with ⟨⟨qheap, qroot⟩, qord⟩; simp only at hQ; subst hQ; exact qord
      rw [OBdd.toTree_node (O := ⟨_, hj_ord⟩) rfl,
          OBdd.toTree_node (O := Q) hQ] at htree_eq
      injection htree_eq with hvar hlo_tree hhi_tree
      have hlo_eq_root := ih_lo
        ⟨⟨Q.1.heap, Q.1.heap[jq].low⟩, OBdd.ordered_of_low_edge hQ_ord⟩
        hP_heap hQ_heap hlo_tree
      have hhi_eq_root := ih_hi
        ⟨⟨Q.1.heap, Q.1.heap[jq].high⟩, OBdd.ordered_of_high_edge hQ_ord⟩
        hP_heap hQ_heap hhi_tree
      have hlo_eq : M[jp].low = M[jq].low := by
        have h1 : P.1.heap[jp].low = Q.1.heap[jq].low := hlo_eq_root
        rw [hP_heap] at h1; rw [hQ_heap] at h1; exact h1
      have hhi_eq : M[jp].high = M[jq].high := by
        have h1 : P.1.heap[jp].high = Q.1.heap[jq].high := hhi_eq_root
        rw [hP_heap] at h1; rw [hQ_heap] at h1; exact h1
      have hvar_eq : M[jp].var = M[jq].var := by
        have h1 : P.1.heap[jp].var = Q.1.heap[jq].var :=
          Fin.ext (congrArg Fin.val hvar)
        rw [hP_heap] at h1; rw [hQ_heap] at h1; exact h1
      exact congrArg _ (node_inj jp jq hvar_eq hlo_eq hhi_eq)
end Reduce
