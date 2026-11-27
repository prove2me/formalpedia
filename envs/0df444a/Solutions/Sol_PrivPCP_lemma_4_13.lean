-- Prove2me | solution 1 for PrivPCP.lemma_4_13
-- status  : ACCEPTED   (disprove)
-- author  : @Shuze Chen
-- created : 2026-11-27T01:20:28.703173+00:00
-- url     : https://prove2.me/submissions/78727399-28a8-441f-b198-d84b75e04374

import Mathlib

namespace PrivPCP.Dis413

lemma exists_subgroup_card {G : Type} [Group G] [Finite G] [IsCyclic G] (d : ℕ)
    (hd : d ∣ Nat.card G) : ∃ H : Subgroup G, Nat.card H = d := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := G)
  have hog : orderOf g = Nat.card G := orderOf_eq_card_of_forall_mem_zpowers hg
  have hpos : 0 < Nat.card G := Nat.card_pos
  have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hd hpos |> fun h => by
    rcases Nat.eq_zero_or_pos d with h0 | h0
    · subst h0; simp at hd; omega
    · exact h0
  obtain ⟨e, he⟩ := hd
  have he0 : e ≠ 0 := by rintro rfl; simp at he; omega
  refine ⟨Subgroup.zpowers (g ^ e), ?_⟩
  rw [Nat.card_zpowers, orderOf_pow' g he0, hog, he]
  rw [Nat.gcd_eq_right (Dvd.intro_left d rfl)]
  exact Nat.mul_div_cancel d (Nat.pos_of_ne_zero he0)

end PrivPCP.Dis413

open PrivPCP.Dis413 MvPolynomial

theorem solution : ¬ (∃ c₀ : ℝ, 0 < c₀ ∧
    ∀ (q : ℕ) [Fact q.Prime] (S₁ S₂ : Subgroup (ZMod q)ˣ),
      Nat.Coprime (Nat.card S₁) (Nat.card S₂) →
      ∀ k₁ k₂ : ℕ, k₁ < Nat.card S₁ → k₂ < Nat.card S₂ →
      ∀ E P : MvPolynomial (Fin 2) (ZMod q), E ≠ 0 →
        (max (E.degreeOf 0) (E.degreeOf 1) : ℝ) ≤
          c₀ * ((min (Nat.card S₁ - k₁) (Nat.card S₂ - k₂) : ℕ) : ℝ) ^ 3 / ((Nat.card S₁ * Nat.card S₂ : ℕ) : ℝ) →
        P.degreeOf 0 < k₁ + E.degreeOf 0 →
        P.degreeOf 1 < k₂ + E.degreeOf 1 →
        (∀ α ∈ S₁, ∃ R : Polynomial (ZMod q),
          MvPolynomial.aeval (![Polynomial.C (α : ZMod q), Polynomial.X] : Fin 2 → Polynomial (ZMod q)) P =
            MvPolynomial.aeval (![Polynomial.C (α : ZMod q), Polynomial.X] : Fin 2 → Polynomial (ZMod q)) E * R) →
        (∀ β ∈ S₂, ∃ Cβ : Polynomial (ZMod q),
          MvPolynomial.aeval (![Polynomial.X, Polynomial.C (β : ZMod q)] : Fin 2 → Polynomial (ZMod q)) P =
            MvPolynomial.aeval (![Polynomial.X, Polynomial.C (β : ZMod q)] : Fin 2 → Polynomial (ZMod q)) E * Cβ) →
        E ∣ P ∧ ∃ Q : MvPolynomial (Fin 2) (ZMod q), P = E * Q ∧ Q.degreeOf 0 < k₁ ∧ Q.degreeOf 1 < k₂) := by
  rintro ⟨c₀, hc₀, h⟩
  -- a large size `m` with `c₀ m² ≥ m + 1`
  obtain ⟨m, hm⟩ := exists_nat_gt (2 / c₀ + 2)
  have hm2 : 2 ≤ m := by
    have : (2 : ℝ) < m := by have := div_pos two_pos hc₀; linarith
    exact_mod_cast this.le
  have hcm : (m : ℝ) + 1 ≤ c₀ * (m : ℝ) ^ 2 / (m + 1) * (m + 1) := by
    have hm0 : (0 : ℝ) < m + 1 := by positivity
    rw [div_mul_cancel₀ _ hm0.ne']
    have h1 : 2 / c₀ < m := by linarith
    have h2 : 2 < c₀ * m := by rwa [div_lt_iff₀ hc₀, mul_comm] at h1
    have h3 : (2 : ℝ) ≤ m := by exact_mod_cast hm2
    nlinarith
  -- a prime `q ≡ 1 (mod m(m+1))`
  obtain ⟨q, hq, -, hqmod⟩ := Nat.exists_prime_gt_modEq_one 1 (show m * (m + 1) ≠ 0 by positivity)
  haveI : Fact q.Prime := ⟨hq⟩
  have hcard : Nat.card (ZMod q)ˣ = q - 1 := by rw [Nat.card_eq_fintype_card, ZMod.card_units]
  have hdvd : m * (m + 1) ∣ q - 1 := by
    have := (Nat.modEq_iff_dvd' hq.one_le).1 hqmod.symm
    exact this
  obtain ⟨S₁, hS₁⟩ := exists_subgroup_card (G := (ZMod q)ˣ) m
    (by rw [hcard]; exact (Dvd.intro _ rfl).trans hdvd)
  obtain ⟨S₂, hS₂⟩ := exists_subgroup_card (G := (ZMod q)ˣ) (m + 1)
    (by rw [hcard]; exact (Dvd.intro_left _ rfl).trans hdvd)
  have hcop : Nat.Coprime (Nat.card S₁) (Nat.card S₂) := by
    rw [hS₁, hS₂]; exact Nat.coprime_self_add_right.2 (Nat.coprime_one_right m)
  set E : MvPolynomial (Fin 2) (ZMod q) := X 0 * X 1 with hE
  have hX0 : (X 0 : MvPolynomial (Fin 2) (ZMod q)) ≠ 0 := X_ne_zero 0
  have hX1 : (X 1 : MvPolynomial (Fin 2) (ZMod q)) ≠ 0 := X_ne_zero 1
  have hE0 : E ≠ 0 := mul_ne_zero hX0 hX1
  have hd0 : E.degreeOf 0 = 1 := by
    rw [hE, degreeOf_mul_eq hX0 hX1, degreeOf_X_self, degreeOf_X_of_ne (by decide)]
  have hd1 : E.degreeOf 1 = 1 := by
    rw [hE, degreeOf_mul_eq hX0 hX1, degreeOf_X_self, degreeOf_X_of_ne (by decide)]
  have := h q S₁ S₂ hcop 0 0 (by rw [hS₁]; omega) (by rw [hS₂]; omega) E 0 hE0 ?_ ?_ ?_ ?_ ?_
  · obtain ⟨-, Q, -, hQ, -⟩ := this
    exact Nat.not_lt_zero _ hQ
  · rw [hd0, hd1, hS₁, hS₂]
    simp only [max_self, Nat.cast_one, Nat.sub_zero]
    have hmin : min m (m + 1) = m := min_eq_left (Nat.le_succ m)
    rw [hmin]
    push_cast
    have hm0 : (0 : ℝ) < m := by positivity
    have hm1 : (0 : ℝ) < m + 1 := by positivity
    rw [le_div_iff₀ (by positivity)]
    have : c₀ * (m : ℝ) ^ 3 = c₀ * (m : ℝ) ^ 2 / (m + 1) * (m + 1) * m := by
      field_simp
    rw [this]
    nlinarith
  · rw [hd0]; simp
  · rw [hd1]; simp
  · intro α _; exact ⟨0, by simp⟩
  · intro β _; exact ⟨0, by simp⟩
