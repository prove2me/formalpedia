-- Prove2me | solution 1 for PartialHomog.Threshold.lemma_E_13_power_sums
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-19T15:21:16.368897+00:00
-- url     : https://prove2.me/submissions/7a2537b0-83ea-4b6a-b1b4-246a617e1991

import Mathlib

open Finset

theorem solution {S : Type*} [CommRing S] :
    (∀ (n M : ℕ) (x y : Fin n → S),
      (∀ k, 1 ≤ k → k ≤ M →
        (Finset.univ.val.map x).esymm k = (Finset.univ.val.map y).esymm k) →
      ∀ p, 1 ≤ p → p ≤ M → ∑ j, x j ^ p = ∑ j, y j ^ p) ∧
    (∀ (n M : ℕ) (x y : Fin n → ℝ), n ≤ M →
      (∀ p, 1 ≤ p → p ≤ M → ∑ j, x j ^ p = ∑ j, y j ^ p) →
      Finset.univ.val.map x = Finset.univ.val.map y) := by
  constructor
  · -- Part 1: equal elementary symmetric functions imply equal power sums (any CommRing)
    intro n M x y hE
    have hNewton : ∀ (z : Fin n → S) (k : ℕ), 0 < k →
        (∑ j, z j ^ k) =
          (-1) ^ (k + 1) * (k : S) * (Finset.univ.val.map z).esymm k -
          ∑ a ∈ Finset.HasAntidiagonal.antidiagonal k with a.1 ∈ Set.Ioo 0 k,
            (-1) ^ a.1 * (Finset.univ.val.map z).esymm a.1 * (∑ j, z j ^ a.2) := by
      intro z k hk
      have hesymm : ∀ i, MvPolynomial.eval z (MvPolynomial.esymm (Fin n) S i) =
          (Finset.univ.val.map z).esymm i := by
        intro i
        have h := MvPolynomial.aeval_esymm_eq_multiset_esymm (σ := Fin n) (R := S) (S := S) i z
        simpa using h
      have h := congrArg (MvPolynomial.eval z)
        (MvPolynomial.psum_eq_mul_esymm_sub_sum (Fin n) S k hk)
      simpa [MvPolynomial.psum, hesymm] using h
    have hP : ∀ p, p ≤ M → (∑ j, x j ^ p) = ∑ j, y j ^ p := by
      intro p
      refine Nat.strong_induction_on p ?_
      intro q ih hqM
      rcases Nat.eq_zero_or_pos q with hq0 | hpos
      · subst hq0
        simp
      · have hes : (Finset.univ.val.map x).esymm q = (Finset.univ.val.map y).esymm q :=
          hE q hpos hqM
        rw [hNewton x q hpos, hNewton y q hpos, hes]
        congr 1
        apply Finset.sum_congr rfl
        intro a ha
        simp only [Finset.mem_filter, Set.mem_Ioo] at ha
        obtain ⟨ha_anti, ha_pos, ha_lt⟩ := ha
        have hes' : (Finset.univ.val.map x).esymm a.1 = (Finset.univ.val.map y).esymm a.1 :=
          hE a.1 ha_pos (le_trans (le_of_lt ha_lt) hqM)
        have hlt : a.2 < q := by
          have := Finset.HasAntidiagonal.mem_antidiagonal.mp ha_anti
          omega
        have hps : (∑ j, x j ^ a.2) = ∑ j, y j ^ a.2 :=
          ih a.2 hlt (le_trans (le_of_lt hlt) hqM)
        rw [hes', hps]
    intro p hp hpM
    exact hP p hpM
  · -- Part 2: equal power sums imply equal multisets over ℝ
    intro n M x y hnM hpowers
    have hpow : ∀ p, p ≤ M → (∑ j, x j ^ p) = ∑ j, y j ^ p := by
      intro p hpM
      rcases Nat.eq_zero_or_pos p with hp0 | hpos
      · subst hp0
        simp
      · exact hpowers p hpos hpM
    have hNewton : ∀ (z : Fin n → ℝ) (k : ℕ),
        (k : ℝ) * (Finset.univ.val.map z).esymm k =
          (-1) ^ (k + 1) *
            ∑ a ∈ Finset.HasAntidiagonal.antidiagonal k with a.1 < k,
              (-1) ^ a.1 * (Finset.univ.val.map z).esymm a.1 * (∑ j, z j ^ a.2) := by
      intro z k
      have hesymm : ∀ i, MvPolynomial.eval z (MvPolynomial.esymm (Fin n) ℝ i) =
          (Finset.univ.val.map z).esymm i := by
        intro i
        have h := MvPolynomial.aeval_esymm_eq_multiset_esymm (σ := Fin n) (R := ℝ) (S := ℝ) i z
        simpa using h
      have h := congrArg (MvPolynomial.eval z) (MvPolynomial.mul_esymm_eq_sum (Fin n) ℝ k)
      simpa [MvPolynomial.psum, hesymm] using h
    have hEeq : ∀ k, k ≤ n → (Finset.univ.val.map x).esymm k = (Finset.univ.val.map y).esymm k := by
      intro k
      refine Nat.strong_induction_on k ?_
      intro q ih hqn
      rcases Nat.eq_zero_or_pos q with hq0 | hqpos
      · subst hq0
        simp [Multiset.esymm]
      · have hx := hNewton x q
        have hy := hNewton y q
        have hsum :
            (∑ a ∈ Finset.HasAntidiagonal.antidiagonal q with a.1 < q,
              (-1) ^ a.1 * (Finset.univ.val.map x).esymm a.1 * (∑ j, x j ^ a.2)) =
            (∑ a ∈ Finset.HasAntidiagonal.antidiagonal q with a.1 < q,
              (-1) ^ a.1 * (Finset.univ.val.map y).esymm a.1 * (∑ j, y j ^ a.2)) := by
          apply Finset.sum_congr rfl
          intro a ha
          simp only [Finset.mem_filter] at ha
          obtain ⟨ha_anti, ha_lt⟩ := ha
          have ha1le : a.1 ≤ n := le_trans (le_of_lt ha_lt) hqn
          have hes : (Finset.univ.val.map x).esymm a.1 = (Finset.univ.val.map y).esymm a.1 :=
            ih a.1 ha_lt ha1le
          have hanti := Finset.HasAntidiagonal.mem_antidiagonal.mp ha_anti
          have ha2M : a.2 ≤ M := by omega
          rw [hes, hpow a.2 ha2M]
        rw [hsum] at hx
        have hk : (q : ℝ) ≠ 0 := by
          exact_mod_cast hqpos.ne'
        exact mul_left_cancel₀ hk (hx.trans hy.symm)
    have hpoly : ((Finset.univ.val.map x).map (fun a => Polynomial.X - Polynomial.C a)).prod =
        ((Finset.univ.val.map y).map (fun a => Polynomial.X - Polynomial.C a)).prod := by
      have hcardx : Multiset.card (Finset.univ.val.map x) = n := by
        rw [Multiset.card_map, ← Finset.card_def]
        simp
      have hcardy : Multiset.card (Finset.univ.val.map y) = n := by
        rw [Multiset.card_map, ← Finset.card_def]
        simp
      rw [Multiset.prod_X_sub_X_eq_sum_esymm, Multiset.prod_X_sub_X_eq_sum_esymm, hcardx, hcardy]
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mem_range] at hj
      rw [hEeq j (by omega)]
    have hroots := congrArg Polynomial.roots hpoly
    rw [Polynomial.roots_multiset_prod_X_sub_C, Polynomial.roots_multiset_prod_X_sub_C] at hroots
    exact hroots
