-- Prove2me | solution 1 for PvsNP.NonuniformPrefixDFA.finite_code_one_pass
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-27T05:33:45.285609+00:00
-- url     : https://prove2.me/submissions/d9d6da24-9ebc-4731-8661-fbf4cba3a70e

import Mathlib

set_option autoImplicit false

namespace PvsNP.NonuniformPrefixDFA

variable {B Code : Type*}

abbrev State (Code : Type*) (length : ℕ) :=
  Option (Fin (length+1) × Code)

def Compatible (decode : Code → List B) (p : List B) : Prop :=
  ∃ c tail, decode c = p ++ tail

noncomputable def compatibleState (decode : Code → List B) (length : ℕ)
    (p : List B) : State Code length := by
  classical
  exact if h : p.length ≤ length ∧ Compatible decode p
    then some (⟨p.length,Nat.lt_succ_of_le h.1⟩,Classical.choose h.2)
    else none

def contents (decode : Code → List B) {length : ℕ} (state : State Code length) :
    Option (List B) :=
  state.map fun (used,c) => (decode c).take used.val

theorem contents_compatibleState (decode : Code → List B) (length : ℕ)
    (maxLength : ∀ c, (decode c).length ≤ length) (p : List B) :
    contents decode (compatibleState decode length p) =
      @ite _ (Compatible decode p) (Classical.propDecidable _) (some p) none := by
  classical
  by_cases h : Compatible decode p
  · have fit : p.length ≤ length := by
      obtain ⟨c,tail,eq⟩ := h
      have bound := maxLength c
      rw [eq,List.length_append] at bound
      omega
    have spec := Classical.choose_spec (show Compatible decode p from h)
    obtain ⟨suffix,decodeEq⟩ := spec
    simp only [compatibleState,dif_pos (And.intro fit h),contents,Option.map_some,if_pos h]
    rw [decodeEq]
    simp
  · simp [compatibleState,contents,h]

noncomputable def update (decode : Code → List B) {length : ℕ}
    (state : State Code length) (bit : B) : State Code length :=
  (contents decode state).bind fun p => compatibleState decode length (p ++ [bit])

noncomputable def start (decode : Code → List B) (length : ℕ) : State Code length :=
  compatibleState decode length []

theorem contents_run (decode : Code → List B) (length : ℕ)
    (maxLength : ∀ c, (decode c).length ≤ length) (word : List B) :
    contents decode (word.foldl (update decode) (start decode length)) =
      @ite _ (Compatible decode word) (Classical.propDecidable _) (some word) none := by
  classical
  induction word using List.reverseRecOn with
  | nil => exact contents_compatibleState decode length maxLength []
  | append_singleton p b ih =>
      rw [List.foldl_append,List.foldl_cons,List.foldl_nil]
      change contents decode ((contents decode (p.foldl (update decode) (start decode length))).bind
        fun prior => compatibleState decode length (prior ++ [b])) = _
      rw [ih]
      by_cases yes : Compatible decode p
      · simp only [if_pos yes,Option.bind_some]
        exact contents_compatibleState decode length maxLength _
      · have no : ¬ Compatible decode (p++[b]) := by
          rintro ⟨c,x,eq⟩
          exact yes ⟨c,[b]++x,by simpa [List.append_assoc] using eq⟩
        simp [yes,no,contents]

def accept (decode : Code → List B) {length : ℕ} (state : State Code length) : Prop :=
  ∃ w, contents decode state = some w ∧ w.length = length

/-- Arbitrary transition tables at a fixed width can check the exact
language of the finite decoder in one symbol transition per output bit. -/
theorem accept_run_iff (decode : Code → List B) (length : ℕ)
    (fixed : ∀ c, (decode c).length = length) (word : List B) :
    accept decode (word.foldl (update decode) (start decode length)) ↔
      ∃ c, decode c = word := by
  have maxLength (c : Code) := (fixed c).le
  unfold accept
  rw [contents_run decode length maxLength word]
  classical
  by_cases yes : Compatible decode word
  · simp only [if_pos yes,Option.some.injEq]
    constructor
    · rintro ⟨_,rfl,equal⟩
      obtain ⟨c,x,eq⟩ := yes
      have empty : x = [] := by
        apply List.length_eq_zero_iff.mp
        have size := fixed c
        rw [eq,List.length_append,equal] at size
        omega
      exact ⟨c,by simpa [empty] using eq⟩
    · rintro ⟨c,eq⟩
      exact ⟨decode c,eq.symm,fixed c⟩
  · simp only [if_neg yes,reduceCtorEq,false_and,exists_false,false_iff]
    intro ⟨c,eq⟩
    exact yes ⟨c,[],by simpa using eq⟩

theorem state_card (Code : Type*) [Fintype Code] (length : ℕ) :
    Fintype.card (State Code length) = (length+1)*Fintype.card Code+1 := by
  simp only [Fintype.card_option,Fintype.card_prod,Fintype.card_fin]

end PvsNP.NonuniformPrefixDFA


theorem solution {B Code : Type*} [Fintype Code] (decode : Code → List B) (length : ℕ)
    (fixed : ∀ c, (decode c).length = length) :
    ∃ (update : Option (Fin (length+1) × Code) → B → Option (Fin (length+1) × Code))
      (initial : Option (Fin (length+1) × Code))
      (accept : Option (Fin (length+1) × Code) → Prop),
      (∀ word, accept (word.foldl update initial) ↔ ∃ c, decode c = word) ∧
      Fintype.card (Option (Fin (length+1) × Code)) = (length+1)*Fintype.card Code+1 := by
  exact ⟨PvsNP.NonuniformPrefixDFA.update decode,PvsNP.NonuniformPrefixDFA.start decode length,
    PvsNP.NonuniformPrefixDFA.accept decode,
    PvsNP.NonuniformPrefixDFA.accept_run_iff decode length fixed,
    PvsNP.NonuniformPrefixDFA.state_card Code length⟩

#print axioms solution
