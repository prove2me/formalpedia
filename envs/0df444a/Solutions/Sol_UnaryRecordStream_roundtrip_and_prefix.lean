-- Prove2me | solution 1 for UnaryRecordStream.roundtrip_and_prefix
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T21:15:27.16175+00:00
-- url     : https://prove2.me/submissions/adfadfc0-2b73-40af-8ecc-590d2259c60e

import Definitions.Def_UnaryRecordStream

set_option autoImplicit false

namespace UnaryRecordStream

private theorem state_prefix (s : ℕ × List ℕ) (x : ℕ) :
    s.2.reverse <+: (step s x).2.reverse := by
  by_cases delimiter : x = 0
  · exact ⟨[s.1], by simp [step,delimiter]⟩
  · simp [step,delimiter]

private theorem fold_prefix (symbols : List ℕ) (s : ℕ × List ℕ) :
    s.2.reverse <+: (symbols.foldl step s).2.reverse := by
  induction symbols generalizing s with
  | nil => simp
  | cons x tail ih => exact (state_prefix s x).trans (ih (step s x))

theorem completed_fields_prefix (left right : List ℕ) :
    fields left <+: fields (left ++ right) := by
  simpa only [fields,List.foldl_append] using fold_prefix right (left.foldl step (0,[]))

private theorem fold_code (n r : ℕ) (rev : List ℕ) :
    (code n).foldl step (r,rev) = (0,(r+n)::rev) := by
  induction n generalizing r with
  | zero => simp [code,step]
  | succ n ih =>
    simp only [code, List.replicate_succ, List.cons_append, List.foldl_cons]
    rw [show step (r,rev) 1 = (r+1,rev) by simp [step]]
    change (code n).foldl step (r+1,rev) = _
    rw [ih, show r+1+n = r+(n+1) by omega]

private theorem fold_encode (values rev : List ℕ) :
    (encode values).foldl step (0,rev) = (0,values.reverse ++ rev) := by
  induction values generalizing rev with
  | nil => simp [encode]
  | cons n tail ih =>
    change (code n ++ encode tail).foldl step (0,rev) = _
    rw [List.foldl_append,fold_code]
    simp [ih]

theorem fields_encode (values : List ℕ) : fields (encode values) = values := by
  simp [fields,fold_encode]

end UnaryRecordStream

open UnaryRecordStream

theorem solution :
    (∀ values, fields (encode values) = values) ∧
    (∀ left right, fields left <+: fields (left ++ right)) ∧
    (∀ values x, x ∈ encode values → x = 0 ∨ x = 1) := by
  refine ⟨fields_encode,completed_fields_prefix,?_⟩
  intro values x present
  obtain ⟨n,_,hit⟩ := List.mem_flatMap.mp present
  simp only [code,List.mem_append,List.mem_singleton] at hit
  exact hit.elim (fun h => Or.inr (List.eq_of_mem_replicate h)) Or.inl

#print axioms solution
