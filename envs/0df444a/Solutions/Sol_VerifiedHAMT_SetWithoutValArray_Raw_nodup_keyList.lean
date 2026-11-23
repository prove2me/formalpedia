-- Prove2me | solution 1 for VerifiedHAMT.SetWithoutValArray.Raw.nodup_keyList
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:51:22.086859+00:00
-- url     : https://prove2.me/submissions/f7254f47-421f-4a4d-8bac-cc978d004576

module
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Basic
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Size
public import Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_keyList_entries
public import Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_keyList_collision
public import Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_mem_entryKeyList
public import Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_mem_keyList
public import Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_DistinctKeys_nodup_toList
attribute [local simp] VerifiedHAMT.SetWithoutValArray.Raw.keyList_collision

set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT VerifiedHAMT.SetWithoutValArray VerifiedHAMT.SetWithoutValArray.Raw
variable {α : Type u}
namespace VerifiedHAMT.SetWithoutValArray.Raw
theorem _root_.solution {hashAt : α → USize} {node : Node α} (wf : WellFormed hashAt node)
    (hu : Unique node) : (keyList node).Nodup := by
  induction wf with
  | collision hashAt keys =>
    cases hu with
    | collision distinct => simpa using distinct.nodup_toList
  | @entries hashAt es size_eq routing children ih =>
    cases hu with
    | entries uchildren =>
      rw [keyList_entries]
      have h_nodup_flatMap : ∀ (l : List (Entry α (Node α))) (offset : Nat),
          (∀ x ∈ l, (entryKeyList x).Nodup) →
          (∀ (i : Nat) (hi : i < l.length) (k : α), k ∈ entryKeyList l[i] → slot (hashAt k) = offset + i) →
          (l.flatMap entryKeyList).Nodup := by
        intro l
        induction l with
        | nil => intro _ _ _; exact List.nodup_nil
        | cons x l ih_l =>
          intro offset parts slots
          rw [List.flatMap_cons, List.nodup_append]
          refine ⟨parts x (List.mem_cons_self ..),
            ih_l (offset + 1)
              (fun y hy => parts y (List.mem_cons_of_mem _ hy))
              (fun i hi k hk => by
                have := slots (i + 1) (by simp; omega) k (by simpa using hk)
                omega), ?_⟩
          intro a ha b hb hab
          subst hab
          have h₁ := slots 0 (by simp) a (by simpa using ha)
          obtain ⟨y, hy, hay⟩ := List.mem_flatMap.mp hb
          obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hy
          have h₂ := slots (j + 1) (by simp; omega) a (by simpa using hay)
          omega
      apply h_nodup_flatMap es.toList 0
      · intro e he
        obtain ⟨i, hi, rfl⟩ := Array.getElem_of_mem (Array.mem_toList_iff.mp he)
        cases hc : es[i] with
        | null => simp [entryKeyList]
        | entry k => simp [entryKeyList]
        | ref c => simpa [entryKeyList] using ih i hi c hc (uchildren i hi c hc)
      · intro i hi k hk
        simp only [Array.length_toList] at hi
        simp only [Array.getElem_toList, Nat.zero_add] at hk ⊢
        exact routing i hi k ((mem_entryKeyList fun c hc =>
          mem_keyList (children i hi c hc) k).mp hk)
end VerifiedHAMT.SetWithoutValArray.Raw
