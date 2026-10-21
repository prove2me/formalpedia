-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P03.lemma6_lastWire
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T10:28:16.893261+00:00
-- url     : https://prove2.me/submissions/76788f44-f9d5-4a04-84be-c4fcfb0b0cb2

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P03
noncomputable section

open QAlgorithms QAlgorithms.Papers.Independent.Claimed50.P03

open MeasureTheory

attribute [local instance] Classical.propDecidable

open scoped BigOperators ComplexConjugate

attribute [local instance] QAlgorithms.Papers.Independent.Claimed50.P03.namedWireMatrixMeasurableSpace

attribute [local instance] QAlgorithms.Papers.Independent.Claimed50.P03.namedWireMatrixBorelSpace


theorem solution (n de : ℕ) (hn : 1 ≤ n) (hde : 1 ≤ de) (hden : de ≤ n)
    (ce : ℝ) (hce : 1 ≤ ce) (H : (Matrix (Qubits n) (Qubits n) ℂ)) (hH : H.IsHermitian)
    (hexp : HasExpansion H ce de) (pi : Equiv.Perm (Fin n)) (i : Fin n) :
    ((Finset.univ.filter fun P : (Fin n → Fin 4) => coefficient H P ≠ 0 ∧
      P (pi i) ≠ 0 ∧ ∀ j : Fin n, i < j → P (pi j) = 0).card : ℝ) ≤
      ce * ((i.val + 1 : ℕ) : ℝ) ^ (de - 1) := by
  set F := (Finset.univ.filter fun P : (Fin n → Fin 4) => coefficient H P ≠ 0 ∧
      P (pi i) ≠ 0 ∧ ∀ j : Fin n, i < j → P (pi j) = 0) with hF
  set T : Finset (Fin n) := Finset.univ.filter fun x => pi.symm x ≤ i with hT
  have hTcard : T.card = i.val + 1 := by
    have : T = (Finset.Iic i).map pi.toEmbedding := by
      ext x; simp only [hT, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
        Finset.mem_Iic, Equiv.toEmbedding_apply]
      constructor
      · intro h; exact ⟨pi.symm x, h, by simp⟩
      · rintro ⟨a, ha, rfl⟩; simpa using ha
    rw [this, Finset.card_map, Fin.card_Iic]
  have hpiT : pi i ∈ T := by simp [hT]
  -- support facts
  have hsuppT : ∀ P ∈ F, wordSupport P ⊆ T := by
    intro P hP x hx
    simp only [hF, Finset.mem_filter, Finset.mem_univ, true_and] at hP
    simp only [wordSupport, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    simp only [hT, Finset.mem_filter, Finset.mem_univ, true_and]
    by_contra h
    push Not at h
    exact hx (by simpa using hP.2.2 _ h)
  have hpisupp : ∀ P ∈ F, pi i ∈ wordSupport P := by
    intro P hP
    simp only [hF, Finset.mem_filter, Finset.mem_univ, true_and] at hP
    simp [wordSupport, hP.2.1]
  set G : Finset (Fin n) → Finset (Fin n → Fin 4) := fun S =>
    Finset.univ.filter fun P : (Fin n → Fin 4) => coefficient H P ≠ 0 ∧
      (S ⊆ wordSupport P ∨ wordSupport P ⊆ S) with hG
  have hcoef : ∀ P ∈ F, coefficient H P ≠ 0 := by
    intro P hP
    simp only [hF, Finset.mem_filter, Finset.mem_univ, true_and] at hP
    exact hP.1
  have key : ∀ (𝒮 : Finset (Finset (Fin n))), (∀ S ∈ 𝒮, S.card = de) → F ⊆ 𝒮.biUnion G →
      (F.card : ℝ) ≤ 𝒮.card * ce := by
    intro 𝒮 h𝒮 hsub
    have h1 := (Finset.card_le_card hsub).trans Finset.card_biUnion_le
    have h1' : (F.card : ℝ) ≤ ∑ S ∈ 𝒮, ((G S).card : ℝ) := by exact_mod_cast h1
    refine h1'.trans ?_
    have := Finset.sum_le_card_nsmul 𝒮 (fun S => ((G S).card : ℝ)) ce
      (fun S hS => hexp S (h𝒮 S hS))
    simpa using this
  have hpow1 : (1 : ℝ) ≤ ((i.val + 1 : ℕ) : ℝ) ^ (de - 1) :=
    one_le_pow₀ (by exact_mod_cast Nat.succ_pos _ |>.nat_succ_le)
  by_cases hcase : de ≤ i.val + 1
  · set 𝒮 := (T.powersetCard de).filter (fun S => pi i ∈ S) with h𝒮
    have hmem : ∀ S ∈ 𝒮, S.card = de ∧ pi i ∈ S ∧ S ⊆ T := by
      intro S hS
      simp only [h𝒮, Finset.mem_filter, Finset.mem_powersetCard] at hS
      exact ⟨hS.1.2, hS.2, hS.1.1⟩
    have hsub : F ⊆ 𝒮.biUnion G := by
      intro P hP
      simp only [Finset.mem_biUnion]
      have hc := hcoef P hP
      by_cases hs : de ≤ (wordSupport P).card
      · obtain ⟨S, h1, h2, h3⟩ := Finset.exists_subsuperset_card_eq
          (Finset.singleton_subset_iff.mpr (hpisupp P hP)) (by simpa using hde) hs
        refine ⟨S, ?_, ?_⟩
        · simp only [h𝒮, Finset.mem_filter, Finset.mem_powersetCard]
          exact ⟨⟨h2.trans (hsuppT P hP), h3⟩, Finset.singleton_subset_iff.mp h1⟩
        · simp only [hG, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨hc, Or.inl h2⟩
      · push Not at hs
        obtain ⟨S, h1, h2, h3⟩ := Finset.exists_subsuperset_card_eq
          (hsuppT P hP) hs.le (by rw [hTcard]; exact hcase)
        refine ⟨S, ?_, ?_⟩
        · simp only [h𝒮, Finset.mem_filter, Finset.mem_powersetCard]
          exact ⟨⟨h2, h3⟩, h1 (hpisupp P hP)⟩
        · simp only [hG, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨hc, Or.inr h1⟩
    have hk := key 𝒮 (fun S hS => (hmem S hS).1) hsub
    have hcard : 𝒮.card ≤ (i.val + 1) ^ (de - 1) := by
      have : 𝒮.card ≤ ((T.erase (pi i)).powersetCard (de - 1)).card := by
        apply Finset.card_le_card_of_injOn (fun S => S.erase (pi i))
        · intro S hS
          obtain ⟨h1, h2, h3⟩ := hmem S hS
          simp only [Finset.mem_coe, Finset.mem_powersetCard]
          refine ⟨Finset.erase_subset_erase _ h3, ?_⟩
          rw [Finset.card_erase_of_mem h2, h1]
        · intro S hS S' hS' h
          have a := (hmem S hS).2.1
          have b := (hmem S' hS').2.1
          simp only at h
          rw [← Finset.insert_erase a, ← Finset.insert_erase b, h]
      rw [Finset.card_powersetCard, Finset.card_erase_of_mem hpiT, hTcard] at this
      refine this.trans ((Nat.choose_le_pow _ _).trans ?_)
      exact Nat.pow_le_pow_left (by omega) _
    have hcR : (𝒮.card : ℝ) ≤ ((i.val + 1 : ℕ) : ℝ) ^ (de - 1) := by exact_mod_cast hcard
    nlinarith
  · push Not at hcase
    obtain ⟨S, h1, -, h3⟩ := Finset.exists_subsuperset_card_eq (n := de)
      (Finset.subset_univ T) (by rw [hTcard]; exact hcase.le) (by simpa using hden)
    have hsub : F ⊆ ({S} : Finset (Finset (Fin n))).biUnion G := by
      intro P hP
      simp only [Finset.singleton_biUnion, hG, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hcoef P hP, Or.inr ((hsuppT P hP).trans h1)⟩
    have hk := key {S} (by simpa using h3) hsub
    simp at hk
    nlinarith

end
