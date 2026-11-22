-- Prove2me | solution 1 for QECCertificates.LRAT.scanAux_spec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:57:32.693593+00:00
-- url     : https://prove2.me/submissions/eb954750-6b15-4a5d-bdf8-497347bc8c61

module
public import Mathlib.Data.List.Basic
public import Mathlib.Data.Nat.Basic
public import Std.Data.TreeMap.Lemmas
public import Std.Data.DTreeMap.Lemmas
public import Definitions.Def_LeanPool_QECCertificates_Reflect_LRAT

set_option autoImplicit true
@[expose] public section
public section
open QECCertificates QECCertificates.LRAT
namespace QECCertificates.LRAT
theorem _root_.solution (a : PAssign) (D : Clause) (fr : List Lit) :
    ∃ tail : List Lit,
      scanAux a fr D = tail ++ fr ∧
        (∀ l ∈ tail, l ∈ D ∧ litFree a l = true) ∧
        (∀ l ∈ D, litFree a l = true → l ∈ tail) := by
  induction D generalizing fr with
  | nil => exact ⟨[], rfl, by simp, by simp⟩
  | cons l rest ih =>
      by_cases hf : litFree a l = true
      · rw [scanAux, if_pos hf]
        obtain ⟨tail, h1, h2, h3⟩ := ih (l :: fr)
        refine ⟨tail ++ [l], ?_, ?_, ?_⟩
        · rw [h1, List.append_assoc, List.singleton_append]
        · intro x hx
          rcases List.mem_append.mp hx with hx | hx
          · exact ⟨List.mem_cons_of_mem _ (h2 x hx).1, (h2 x hx).2⟩
          · rw [List.mem_singleton] at hx
            subst hx
            exact ⟨by simp, hf⟩
        · intro x hx hx'
          rcases List.mem_cons.mp hx with rfl | hx
          · exact List.mem_append_right _ (by simp)
          · exact List.mem_append_left _ (h3 x hx hx')
      · rw [scanAux, if_neg hf]
        obtain ⟨tail, h1, h2, h3⟩ := ih fr
        exact ⟨tail, h1, fun x hx => ⟨List.mem_cons_of_mem _ (h2 x hx).1, (h2 x hx).2⟩,
          fun x hx hx' => by
            rcases List.mem_cons.mp hx with rfl | hx
            · exact absurd hx' hf
            · exact h3 x hx hx'⟩
end QECCertificates.LRAT
