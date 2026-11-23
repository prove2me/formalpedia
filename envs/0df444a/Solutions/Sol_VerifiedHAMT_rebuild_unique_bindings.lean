-- Prove2me | solution 1 for VerifiedHAMT.rebuild_unique_bindings
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:40:19.904965+00:00
-- url     : https://prove2.me/submissions/779746e1-7382-4c4a-a1d7-026c3f365a29

module
public import Definitions.Def_VerifiedHAMT_Insert
public import Definitions.Def_VerifiedHAMT_Size
public import Definitions.Def_VerifiedHAMT_Util
public import Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashMap
public import Init.Data.Array.Basic
import all Init.Data.Array.Basic
public import Definitions.Def_VerifiedHAMT_InsertProofs
public import Theorems.Thm_VerifiedHAMT_insertEntries_wf_mem
public import Theorems.Thm_VerifiedHAMT_insertEntries_unique_updated
public import Theorems.Thm_VerifiedHAMT_EntryHasBinding_hasKey
public import Theorems.Thm_VerifiedHAMT_HasBinding_hasKey


set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT
open Lean.PersistentHashMap
variable {α : Type u} {β : Type v}
namespace VerifiedHAMT
theorem _root_.solution [BEq α] [LawfulBEq α] [Hashable α]
    (childInsert : Node α β → USize → α → β → Node α β) (offset : USize)
    (childWF :
      letI hashAt := fun q : α => nextHash ((hash q).toUSize >>> offset)
      ∀ n, WellFormed hashAt n → ∀ k v,
        letI res := childInsert n (hashAt k) k v
        WellFormed hashAt res ∧ ∀ q, HasKey q res ↔ q = k ∨ HasKey q n)
    (childUpd :
      letI hashAt := fun q : α => nextHash ((hash q).toUSize >>> offset)
      ∀ n, WellFormed hashAt n → Unique n → ∀ k v,
        letI res := childInsert n (hashAt k) k v
        Unique res ∧ Updated n res k v)
    (keys : Array α) (vals : Array β) (hsz : keys.size = vals.size)
    (distinct : DistinctKeys keys) (i : Nat)
    (es : Array (Entry α β (Node α β)))
    (wf : WellFormed (fun q => (hash q).toUSize >>> offset) (.entries es)) (hu : Unique (.entries es))
    (disjoint : ∀ (j : Nat) (hj : j < keys.size), i ≤ j → ¬ HasKey keys[j] (.entries es)) :
    letI res := rebuild childInsert offset ⟨.collision keys vals hsz, .mk ..⟩ i es
    Unique (.entries res) ∧
      ∀ q w, HasBinding q w (.entries res) ↔
        HasBinding q w (.entries es) ∨
          ∃ (j : Nat) (hj : j < keys.size), i ≤ j ∧ keys[j] = q ∧ vals[j]'(hsz ▸ hj) = w := by
  rw [rebuild.eq_def]
  dsimp only
  split
  · rename_i hi
    have stepWM := insertEntries_wf_mem (fun q => (hash q).toUSize >>> offset) es
      (fun child _ => childInsert child) keys[i]
      (vals[i]'(hsz ▸ hi)) wf (by
        cases wf <;> grind [Array.mem_iff_getElem])
    have stepUV := insertEntries_unique_updated (fun q => (hash q).toUSize >>> offset) es
      (fun child _ => childInsert child) keys[i]
      (vals[i]'(hsz ▸ hi)) wf hu (by
        cases wf <;> grind [Array.mem_iff_getElem])
    have nextDisjoint : ∀ (j : Nat) (hj : j < keys.size), i + 1 ≤ j →
        ¬ HasKey keys[j] (.entries (insertEntries es (fun child _ => childInsert child)
          ((hash keys[i]).toUSize >>> offset) keys[i] (vals[i]'(hsz ▸ hi)))) := by
      intro j hj hij
      rw [stepWM.2]
      grind [DistinctKeys]
    obtain ⟨hu', hb'⟩ := solution childInsert offset childWF childUpd
      keys vals hsz distinct (i + 1) _ stepWM.1 stepUV.1 nextDisjoint
    refine ⟨hu', ?_⟩
    intro q w
    rw [hb', stepUV.2]
    grind [HasBinding.hasKey]
  · exact ⟨hu, by grind⟩
termination_by keys.size - i
end VerifiedHAMT
