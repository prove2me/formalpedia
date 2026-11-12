-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakethird100.P06.classicalBit_unlimitedSharing
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-11T22:18:19.724196+00:00
-- url     : https://prove2.me/submissions/01dca723-9fde-4d70-8d93-fda5ad1a4380

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P06

noncomputable section

open scoped BigOperators

open QAlgorithms.Papers.Independent.Dependency50.P33 (NuclearExpansion)

open QAlgorithms.Papers.Independent.Frontier18.P09 (partialTraceRightCoeff)

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Intakethird100.P06 in
theorem solution (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (n : ℕ) (hn : 1 ≤ n) :
    (∀ x, 0 ≤ sharedBitLaw n p x) ∧
    (∑ x : Fin n → Bool, sharedBitLaw n p x) = 1 ∧
    (∀ (i : Fin n) (b : Bool),
      (∑ x : Fin n → Bool, if x i = b then sharedBitLaw n p x else 0) =
        if b then 1 - p else p) ∧
    (∑ x : Fin n → Bool,
      if ∀ i j : Fin n, x i = x j then sharedBitLaw n p x else 0) = 1 := by
  have hFT : (fun _ => false : Fin n → Bool) ≠ (fun _ => true) := by
    intro h
    have := congrFun h ⟨0, hn⟩
    simp at this
  have LF : sharedBitLaw n p (fun _ => false) = p := by
    unfold sharedBitLaw
    rw [if_pos rfl, if_neg hFT, add_zero]
  have LT : sharedBitLaw n p (fun _ => true) = 1 - p := by
    unfold sharedBitLaw
    rw [if_neg (Ne.symm hFT), if_pos rfl, zero_add]
  have L0 : ∀ c : Fin n → Bool, c ≠ (fun _ => false) ∧ c ≠ (fun _ => true) →
      sharedBitLaw n p c = 0 := by
    rintro c ⟨h1, h2⟩
    unfold sharedBitLaw
    rw [if_neg h1, if_neg h2, add_zero]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x
    unfold sharedBitLaw
    split_ifs <;> linarith
  · refine (Finset.sum_eq_add (s := Finset.univ) (fun _ => false) (fun _ => true) hFT
      ?_ ?_ ?_).trans ?_
    · intro c _ hc
      exact L0 c hc
    · intro h; exact absurd (Finset.mem_univ _) h
    · intro h; exact absurd (Finset.mem_univ _) h
    · rw [LF, LT]; ring
  · intro i b
    refine (Finset.sum_eq_add (s := Finset.univ) (fun _ => false) (fun _ => true) hFT
      ?_ ?_ ?_).trans ?_
    · intro c _ hc
      simp only [L0 c hc, ite_self]
    · intro h; exact absurd (Finset.mem_univ _) h
    · intro h; exact absurd (Finset.mem_univ _) h
    · rcases b with _ | _ <;> simp [LF, LT]
  · refine (Finset.sum_eq_add (s := Finset.univ) (fun _ => false) (fun _ => true) hFT
      ?_ ?_ ?_).trans ?_
    · intro c _ hc
      simp only [L0 c hc, ite_self]
    · intro h; exact absurd (Finset.mem_univ _) h
    · intro h; exact absurd (Finset.mem_univ _) h
    · simp [LF, LT]

end
