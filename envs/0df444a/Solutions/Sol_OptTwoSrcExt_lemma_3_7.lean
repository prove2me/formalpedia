-- Prove2me | solution 1 for OptTwoSrcExt.lemma_3_7
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-21T08:38:04.19951+00:00
-- url     : https://prove2.me/submissions/9167e63d-fa41-40f6-98de-6b3b89117c86

import Mathlib

theorem solution {F : Type*} [Field F] [CharP F 2] [DecidableEq F] (D : ℕ) (hD : ∃ j : ℕ, D = 2 ^ j) :
    (∀ (z : Fin (2 * D - 1) → F) (α : F) (S : Finset (Fin (2 * D - 1))),
        S.card = D → (∀ i ∈ S, z i = α) →
          (Finset.univ.val.map z).esymm D = α ^ D) ∧
    (∀ z : Fin (2 * D - 1) → F, (∀ i, z i = 0 ∨ z i = 1) →
        (Finset.univ.val.map z).esymm D =
          if 2 * D - 1 < 2 * (Finset.univ.filter fun i => z i = 1).card then 1 else 0) := by
  classical
  obtain ⟨j, rfl⟩ := hD
  have hD1 : 1 ≤ 2 ^ j := Nat.one_le_pow j 2 (by norm_num)
  -- the coefficient identity relating `esymm` to the product of linear factors
  have hcoeff : ∀ z : Fin (2 * 2 ^ j - 1) → F,
      (∏ i : Fin (2 * 2 ^ j - 1), (Polynomial.X + Polynomial.C (z i))).coeff (2 ^ j - 1) =
        (Finset.univ.val.map z).esymm (2 ^ j) := by
    intro z
    have h1 := Finset.prod_X_add_C_coeff (Finset.univ : Finset (Fin (2 * 2 ^ j - 1))) z
      (k := 2 ^ j - 1) (by rw [Finset.card_univ, Fintype.card_fin]; omega)
    rw [Finset.card_univ, Fintype.card_fin] at h1
    rw [show 2 * 2 ^ j - 1 - (2 ^ j - 1) = 2 ^ j by omega] at h1
    rw [h1, Finset.esymm_map_val]
  constructor
  · -- ## Part 1: `D` coordinates equal to `α`
    intro z α S hScard hSconst
    rw [← hcoeff z]
    -- monicity and degree of the complementary product
    have hQmonic : (∏ i ∈ Sᶜ, (Polynomial.X + Polynomial.C (z i))).Monic :=
      Polynomial.monic_prod_of_monic _ _ (fun i _ => Polynomial.monic_X_add_C _)
    have hQdeg : (∏ i ∈ Sᶜ, (Polynomial.X + Polynomial.C (z i))).natDegree = 2 ^ j - 1 := by
      rw [Polynomial.natDegree_prod_of_monic (s := Sᶜ)
        (f := fun i => Polynomial.X + Polynomial.C (z i)) (fun i _ => Polynomial.monic_X_add_C _)]
      simp only [Polynomial.natDegree_X_add_C, Finset.sum_const, Finset.card_compl,
        Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
      rw [hScard]
      omega
    have hQcoeff : (∏ i ∈ Sᶜ, (Polynomial.X + Polynomial.C (z i))).coeff (2 ^ j - 1) = 1 := by
      rw [← hQdeg]
      exact hQmonic.coeff_natDegree
    -- split the product at `S`
    have hprodS : (∏ i ∈ S, (Polynomial.X + Polynomial.C (z i))) =
        (Polynomial.X + Polynomial.C α) ^ (2 ^ j) := by
      calc (∏ i ∈ S, (Polynomial.X + Polynomial.C (z i))) =
          ∏ i ∈ S, (Polynomial.X + Polynomial.C α) := by
            apply Finset.prod_congr rfl
            intro i hi
            rw [hSconst i hi]
        _ = (Polynomial.X + Polynomial.C α) ^ S.card := by rw [Finset.prod_const]
        _ = (Polynomial.X + Polynomial.C α) ^ (2 ^ j) := by rw [hScard]
    have hsplit : (∏ i : Fin (2 * 2 ^ j - 1), (Polynomial.X + Polynomial.C (z i))) =
        (Polynomial.X + Polynomial.C α) ^ (2 ^ j) *
          ∏ i ∈ Sᶜ, (Polynomial.X + Polynomial.C (z i)) := by
      rw [← Finset.prod_mul_prod_compl S (fun i => Polynomial.X + Polynomial.C (z i))]
      rw [hprodS]
    -- freshman's dream
    have hfresh : (Polynomial.X + Polynomial.C α) ^ (2 ^ j) =
        Polynomial.X ^ (2 ^ j) + Polynomial.C (α ^ (2 ^ j)) := by
      have h := add_pow_char_pow (Polynomial.X : Polynomial F) (Polynomial.C α) 2 j
      simpa using h
    have hprod : (∏ i : Fin (2 * 2 ^ j - 1), (Polynomial.X + Polynomial.C (z i))) =
        Polynomial.X ^ (2 ^ j) * ∏ i ∈ Sᶜ, (Polynomial.X + Polynomial.C (z i)) +
          Polynomial.C (α ^ (2 ^ j)) * ∏ i ∈ Sᶜ, (Polynomial.X + Polynomial.C (z i)) := by
      rw [hsplit, hfresh, add_mul]
    have hzero : (Polynomial.X ^ (2 ^ j) *
          ∏ i ∈ Sᶜ, (Polynomial.X + Polynomial.C (z i))).coeff (2 ^ j - 1) = 0 := by
      rw [Polynomial.coeff_X_pow_mul']
      have hnot : ¬ (2 ^ j ≤ 2 ^ j - 1) := by omega
      simp [hnot]
    have hone : (Polynomial.C (α ^ (2 ^ j)) *
          ∏ i ∈ Sᶜ, (Polynomial.X + Polynomial.C (z i))).coeff (2 ^ j - 1) = α ^ (2 ^ j) := by
      rw [Polynomial.coeff_C_mul, hQcoeff, mul_one]
    rw [hprod, Polynomial.coeff_add, hzero, hone, zero_add]
  · -- ## Part 2: `z` takes values in `{0, 1}`
    intro z hz
    rw [← hcoeff z]
    set O : Finset (Fin (2 * 2 ^ j - 1)) := Finset.univ.filter (fun i => z i = 1) with hO
    set Zc : Finset (Fin (2 * 2 ^ j - 1)) := Finset.univ.filter (fun i => z i = 0) with hZ
    have hObound : O.card ≤ 2 * 2 ^ j - 1 := by
      have h := Finset.card_le_univ O
      simpa using h
    have hZbound : Zc.card ≤ 2 * 2 ^ j - 1 := by
      have h := Finset.card_le_univ Zc
      simpa using h
    have hcompl : Zcᶜ = O := by
      ext i
      simp only [hZ, hO, Finset.mem_compl, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro h
        rcases hz i with h0 | h1
        · exact absurd h0 h
        · exact h1
      · intro h
        rw [h]
        exact one_ne_zero
    have hZc : ∀ i ∈ Zc, z i = 0 := fun i hi => by
      simpa [hZ] using (Finset.mem_filter.mp hi).2
    have hOc : ∀ i ∈ O, z i = 1 := fun i hi => by
      simpa [hO] using (Finset.mem_filter.mp hi).2
    have hsplit : (∏ i : Fin (2 * 2 ^ j - 1), (Polynomial.X + Polynomial.C (z i))) =
        Polynomial.X ^ (Zc.card) * (Polynomial.X + Polynomial.C (1 : F)) ^ (O.card) := by
      rw [← Finset.prod_mul_prod_compl Zc (fun i => Polynomial.X + Polynomial.C (z i)), hcompl]
      congr 1
      · rw [Finset.prod_congr rfl (fun i hi => by rw [hZc i hi])]
        simp only [Polynomial.C_0, add_zero]
        rw [Finset.prod_const]
      · rw [Finset.prod_congr rfl (fun i hi => by rw [hOc i hi])]
        rw [Finset.prod_const]
    rw [hsplit]
    have hZcard : Zc.card = 2 * 2 ^ j - 1 - O.card := by
      have h := Finset.card_compl (s := Zc)
      rw [hcompl, Fintype.card_fin] at h
      omega
    rw [hZcard]
    -- now the coefficient of `X^(N-m) * (X+1)^m` at `D-1`
    by_cases hm : O.card < 2 ^ j
    · -- `m < D`: the coefficient vanishes
      have hzero : (Polynomial.X ^ (2 * 2 ^ j - 1 - O.card) *
            (Polynomial.X + Polynomial.C (1 : F)) ^ O.card).coeff (2 ^ j - 1) = 0 := by
        rw [Polynomial.coeff_X_pow_mul']
        have hnot : ¬ (2 * 2 ^ j - 1 - O.card ≤ 2 ^ j - 1) := by omega
        simp [hnot]
      rw [hzero]
      have hif : ¬ (2 * 2 ^ j - 1 < 2 * O.card) := by omega
      rw [if_neg hif]
    · -- `m ≥ D`: the coefficient is one
      push_neg at hm
      have hle : 2 * 2 ^ j - 1 - O.card ≤ 2 ^ j - 1 := by omega
      rw [Polynomial.coeff_X_pow_mul']
      rw [if_pos hle]
      set r : ℕ := O.card - 2 ^ j with hr
      have hmr : O.card = 2 ^ j + r := by omega
      have hc : ((Polynomial.X + Polynomial.C (1 : F)) ^ O.card).coeff (O.card - 2 ^ j) = 1 := by
        have hsub : 2 ^ j + r - 2 ^ j = r := by omega
        rw [hmr, hsub, pow_add]
        have hfresh : (Polynomial.X + Polynomial.C (1 : F)) ^ (2 ^ j) =
            Polynomial.X ^ (2 ^ j) + 1 := by
          have h := add_pow_char_pow (Polynomial.X : Polynomial F) (Polynomial.C (1 : F)) 2 j
          simpa using h
        rw [hfresh, add_mul, Polynomial.coeff_add]
        have h0 : (Polynomial.X ^ (2 ^ j) *
              (Polynomial.X + Polynomial.C (1 : F)) ^ r).coeff r = 0 := by
          rw [Polynomial.coeff_X_pow_mul']
          have hnot : ¬ (2 ^ j ≤ r) := by omega
          simp [hnot]
        have h1 : ((1 : Polynomial F) * (Polynomial.X + Polynomial.C (1 : F)) ^ r).coeff r = 1 := by
          rw [one_mul]
          have hmonic : ((Polynomial.X + Polynomial.C (1 : F)) ^ r).Monic :=
            (Polynomial.monic_X_add_C 1).pow r
          have hdeg : ((Polynomial.X + Polynomial.C (1 : F)) ^ r).natDegree = r := by
            rw [Polynomial.Monic.natDegree_pow (Polynomial.monic_X_add_C 1),
              Polynomial.natDegree_X_add_C]
            simp
          have hcd := hmonic.coeff_natDegree
          rwa [hdeg] at hcd
        rw [h0, h1, zero_add]
      rw [show 2 ^ j - 1 - (2 * 2 ^ j - 1 - O.card) = O.card - 2 ^ j by omega]
      rw [hc]
      have hif : 2 * 2 ^ j - 1 < 2 * O.card := by omega
      rw [if_pos hif]

