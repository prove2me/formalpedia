-- Prove2me | solution 1 for OBdd.discover_spec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:08:35.143396+00:00
-- url     : https://prove2.me/submissions/e64f71d8-3f31-4692-88ac-41c9941334ba

import Definitions.Def_Bdd_Collect
import Definitions.Def_Bdd_Reduce_Discover
import Theorems.Thm_Collect_collect_spec
import Theorems.Thm_Nary_restrict_const
attribute [local simp] Nary.restrict_const


section
set_option autoImplicit true
open Pointer
open Bdd
private lemma OBdd.discover_helper_retains_found {I : Vector (List (Fin m)) n} {i : Fin n} : j ∈ I[i] → j ∈ (OBdd.discover_helper l v I)[i] := by
  induction l generalizing I with
  | nil => exact id
  | cons head tail ih =>
    intro h
    unfold OBdd.discover_helper
    apply ih
    rcases eq_or_ne (v[head].var) i with heq | hne
    · have hkey : (I.set (v[head].var) (head :: I[v[head].var]))[i] = head :: I[i] := by
        subst heq; simp [Vector.getElem_set_self]
      simp only [hkey]; exact List.mem_cons_of_mem _ h
    · have hkey : (I.set (v[head].var) (head :: I[v[head].var]))[i] = I[i] :=
        Vector.getElem_set_ne _ _ (Fin.val_ne_of_ne hne)
      simp only [hkey]; exact h
private lemma OBdd.discover_helper_spec (O : OBdd n m) {I : Vector (List (Fin m)) n} :
    j ∈ l → j ∈ (OBdd.discover_helper l v I)[v[j].var] := by
  intro h
  cases h with
  | head as =>
    unfold OBdd.discover_helper
    apply OBdd.discover_helper_retains_found
    simp [Vector.getElem_set_self]
  | tail b ih =>
    unfold OBdd.discover_helper
    exact OBdd.discover_helper_spec O ih
end

set_option autoImplicit true
open Pointer
open Bdd
namespace OBdd
theorem _root_.solution {O : OBdd n m} {j : Fin m} :
    (Reachable O.1.heap O.1.root (node j)) → j ∈ (OBdd.discover O)[O.1.heap[j].var] :=
  (OBdd.discover_helper_spec O) ∘ Collect.collect_spec
end OBdd
