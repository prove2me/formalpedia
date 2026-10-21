-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P03.fact2_expansion
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T10:25:31.470172+00:00
-- url     : https://prove2.me/submissions/f8a5d224-e088-49df-a593-b26f8c131ffd

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

lemma g58a_coef_sum {n m : ℕ} (T : Fin m → Matrix (Qubits n) (Qubits n) ℂ) (P : Fin n → Fin 4) :
    coefficient (∑ j, T j) P = ∑ j, coefficient (T j) P := by
  simp only [coefficient, Matrix.mul_sum, Matrix.trace_sum, Complex.re_sum, Finset.sum_div]

theorem solution (n k d : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k) (hd : 1 ≤ d)
    (H : (Matrix (Qubits n) (Qubits n) ℂ)) (hH : H.IsHermitian) (hdeg : HasBoundedDegree k d H) :
    HasExpansion H ((4 : ℝ) ^ k * (d : ℝ)) 1 := by
  obtain ⟨m, S, T, hHT, hT, hdegS⟩ := hdeg
  intro U hU
  obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp hU
  set F := (Finset.univ.filter fun P : (Fin n → Fin 4) => coefficient H P ≠ 0 ∧
      ({i} ⊆ wordSupport P ∨ wordSupport P ⊆ {i})) with hF
  have hex : ∀ P ∈ F, ∃ j, wordSupport P ⊆ S j := by
    intro P hP
    simp only [hF, Finset.mem_filter, Finset.mem_univ, true_and] at hP
    rw [hHT, g58a_coef_sum] at hP
    obtain ⟨j, -, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero hP.1
    exact ⟨j, by by_contra h; exact hj ((hT j).2.2 P h)⟩
  set J := Finset.univ.filter fun j => i ∈ S j with hJ
  have hJd : J.card ≤ d := hdegS i
  by_cases hJe : J.Nonempty
  · obtain ⟨j0, hj0⟩ := hJe
    have hsub : F ⊆ J.biUnion (fun j => Finset.univ.filter fun P : (Fin n → Fin 4) =>
        wordSupport P ⊆ S j) := by
      intro P hP
      obtain ⟨j, hj⟩ := hex P hP
      simp only [hF, Finset.mem_filter, Finset.mem_univ, true_and] at hP
      simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
      rcases hP.2 with h | h
      · refine ⟨j, ?_, hj⟩
        simp only [hJ, Finset.mem_filter, Finset.mem_univ, true_and]
        exact hj (h (Finset.mem_singleton_self i))
      · refine ⟨j0, hj0, h.trans ?_⟩
        simp only [hJ, Finset.mem_filter, Finset.mem_univ, true_and] at hj0
        simpa using hj0
    have h1 := (Finset.card_le_card hsub).trans Finset.card_biUnion_le
    have h2 : ∑ j ∈ J, (Finset.univ.filter fun P : (Fin n → Fin 4) =>
        wordSupport P ⊆ S j).card ≤ J.card • 4 ^ k := by
      apply Finset.sum_le_card_nsmul
      intro j _
      exact (g58a_card_supp_le (S j)).trans (Nat.pow_le_pow_right (by norm_num) (hT j).2.1)
    have h3 : F.card ≤ 4 ^ k * d := by
      rw [smul_eq_mul] at h2
      calc F.card ≤ J.card * 4 ^ k := h1.trans h2
        _ ≤ d * 4 ^ k := Nat.mul_le_mul_right _ hJd
        _ = 4 ^ k * d := by ring
    exact_mod_cast h3
  · have hsub : F ⊆ {fun _ => 0} := by
      intro P hP
      obtain ⟨j, hj⟩ := hex P hP
      simp only [hF, Finset.mem_filter, Finset.mem_univ, true_and] at hP
      have hi : P i = 0 := by
        by_contra h
        have : i ∈ S j := hj (by simp [wordSupport, h])
        exact hJe ⟨j, by simp [hJ, this]⟩
      rcases hP.2 with h | h
      · have := h (Finset.mem_singleton_self i)
        simp [wordSupport, hi] at this
      · simp only [Finset.mem_singleton]
        funext x
        by_contra hx
        have := h (by simp [wordSupport, hx] : x ∈ wordSupport P)
        rw [Finset.mem_singleton] at this
        subst this; exact hx hi
    have h1 := Finset.card_le_card hsub
    rw [Finset.card_singleton] at h1
    have : (1 : ℝ) ≤ 4 ^ k * d := by
      have : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
      nlinarith [one_le_pow₀ (show (1 : ℝ) ≤ 4 by norm_num) (n := k)]
    calc (F.card : ℝ) ≤ 1 := by exact_mod_cast h1
      _ ≤ _ := this

end
