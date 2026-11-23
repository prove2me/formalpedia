-- Prove2me | solution 1 for OBdd.discover_spec_inv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:08:42.37795+00:00
-- url     : https://prove2.me/submissions/480d025a-2f6a-41d1-88a6-4bb39bf4d95d

import Definitions.Def_Bdd_Collect
import Definitions.Def_Bdd_Reduce_Discover
import Theorems.Thm_Collect_collect_spec_reverse
import Theorems.Thm_Nary_restrict_const
attribute [local simp] Nary.restrict_const


section
set_option autoImplicit true
open Pointer
open Bdd
private lemma OBdd.discover_helper_mem_var {l : List (Fin m)} {v : Vector (Node n m) m}
    {I : Vector (List (Fin m)) n} {i : Fin n} {j : Fin m} :
    j ∈ (OBdd.discover_helper l v I)[i] → j ∈ I[i] ∨ (j ∈ l ∧ v[j].var = i) := by
  induction l generalizing I with
  | nil => exact .inl
  | cons head tail ih =>
    simp only [OBdd.discover_helper]
    intro h
    rcases ih h with h | ⟨hmem, hvar⟩
    · rcases eq_or_ne (v[head].var) i with heq | hne
      · have hkey : (I.set (v[head].var) (head :: I[v[head].var]))[i] = head :: I[i] := by
          subst heq; simp [Vector.getElem_set_self]
        rw [hkey] at h
        simp only [List.mem_cons] at h
        rcases h with rfl | h
        · exact .inr ⟨.head _, heq⟩
        · exact .inl h
      · have hkey : (I.set (v[head].var) (head :: I[v[head].var]))[i] = I[i] :=
          Vector.getElem_set_ne _ _ (Fin.val_ne_of_ne hne)
        rw [hkey] at h
        exact .inl h
    · exact .inr ⟨.tail _ hmem, hvar⟩
end

set_option autoImplicit true
open Pointer
open Bdd
namespace OBdd
theorem _root_.solution {O : OBdd n m} {j : Fin m} {i : Fin n} :
    j ∈ (OBdd.discover O)[i] →
    O.1.heap[j].var.1 = i.1 ∧ Reachable O.1.heap O.1.root (.node j) := by
  simp only [OBdd.discover, Fin.getElem_fin]
  intro h
  rcases OBdd.discover_helper_mem_var h with h | ⟨hmem, hvar⟩
  · simp [Vector.getElem_replicate] at h
  · exact ⟨congrArg Fin.val hvar, Collect.collect_spec_reverse hmem⟩
end OBdd
