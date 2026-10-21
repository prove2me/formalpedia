-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P03.fact1_expansion
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T10:24:12.508164+00:00
-- url     : https://prove2.me/submissions/07d52538-86a1-4c06-8801-c68ab62a1b5b

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P03
noncomputable section

open QAlgorithms QAlgorithms.Papers.Independent.Claimed50.P03

open MeasureTheory

attribute [local instance] Classical.propDecidable

open scoped BigOperators ComplexConjugate

attribute [local instance] QAlgorithms.Papers.Independent.Claimed50.P03.namedWireMatrixMeasurableSpace

attribute [local instance] QAlgorithms.Papers.Independent.Claimed50.P03.namedWireMatrixBorelSpace

lemma g58a_card_supp_le {n : ℕ} (S : Finset (Fin n)) :
    (Finset.univ.filter fun P : (Fin n → Fin 4) => wordSupport P ⊆ S).card ≤ 4 ^ S.card := by
  have h : (Finset.univ.filter fun P : (Fin n → Fin 4) => wordSupport P ⊆ S).card ≤
      (Finset.univ : Finset (S → Fin 4)).card := by
    apply Finset.card_le_card_of_injOn (fun P (x : S) => P x.1)
    · intro P _; simp
    · intro P hP Q hQ hPQ
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hP hQ
      funext i
      by_cases hi : i ∈ S
      · exact congrFun hPQ ⟨i, hi⟩
      · have h1 : P i = 0 := by
          by_contra h; exact hi (hP (by simp [wordSupport, h]))
        have h2 : Q i = 0 := by
          by_contra h; exact hi (hQ (by simp [wordSupport, h]))
        rw [h1, h2]
  simpa [Fintype.card_fun] using h

theorem solution (n k : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k)
    (H : (Matrix (Qubits n) (Qubits n) ℂ)) (hH : H.IsHermitian) (hloc : IsLocal k H) :
    HasExpansion H ((4 : ℝ) ^ k) k := by
  intro S hS
  have hsub : (Finset.univ.filter fun P : (Fin n → Fin 4) => coefficient H P ≠ 0 ∧
      (S ⊆ wordSupport P ∨ wordSupport P ⊆ S)) ⊆
      (Finset.univ.filter fun P : (Fin n → Fin 4) => wordSupport P ⊆ S) := by
    intro P hP
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hP ⊢
    obtain ⟨hc, h | h⟩ := hP
    · have hw : pauliWeight P ≤ k := by
        by_contra hw; exact hc (hloc P (by omega))
      have : S = wordSupport P :=
        Finset.eq_of_subset_of_card_le h (by rw [hS]; exact hw)
      rw [this]
    · exact h
  have := (Finset.card_le_card hsub).trans (g58a_card_supp_le S)
  rw [hS] at this
  exact_mod_cast this

end
