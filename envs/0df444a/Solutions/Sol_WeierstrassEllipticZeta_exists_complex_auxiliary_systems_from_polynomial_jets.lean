-- Prove2me | solution 1 for WeierstrassEllipticZeta.exists_complex_auxiliary_systems_from_polynomial_jets
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-07T11:38:20.784363+00:00
-- url     : https://prove2.me/submissions/77989c39-25b8-4818-9366-9a29516f6dc5

import Definitions.Def_WeierstrassEllipticZeta_DifferentialPolynomials
import Theorems.Thm_TranscendenceTheory_polynomial_derivation_length_bound
import Theorems.Thm_WeierstrassEllipticZeta_exists_complex_auxiliary_systems_from_bounded_polynomial_jets
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr

noncomputable section

open MvPolynomial

namespace WeierstrassEllipticZeta

private def polyLength {σ : Type} (p : MvPolynomial σ ℤ) : ℕ :=
  ∑ m ∈ p.support, (p.coeff m).natAbs

private lemma polyLength_eq {σ : Type} (p : MvPolynomial σ ℤ) :
    polyLength p = ∑ m ∈ p.support, (p.coeff m).natAbs := rfl

private lemma polyLength_sum_le {σ ι : Type} (s : Finset ι)
    (f : ι → MvPolynomial σ ℤ) :
    polyLength (∑ i ∈ s, f i) ≤ ∑ i ∈ s, polyLength (f i) := by
  classical
  let t := s.biUnion fun i => (f i).support
  have heq (p : MvPolynomial σ ℤ) (hp : p.support ⊆ t) :
      polyLength p = ∑ m ∈ t, (p.coeff m).natAbs := by
    rw [polyLength_eq]
    apply Finset.sum_subset hp
    intro m _ hm
    simp [notMem_support_iff.mp hm]
  rw [heq _ support_sum]
  simp_rw [coeff_sum]
  calc
    _ ≤ ∑ m ∈ t, ∑ i ∈ s, ((f i).coeff m).natAbs := by
      apply Finset.sum_le_sum
      intro m _
      exact Int.natAbs_sum_le _ _
    _ = ∑ i ∈ s, polyLength (f i) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      exact (heq _ (Finset.subset_biUnion_of_mem (fun i => (f i).support) hi)).symm

private lemma polyLength_monomial {σ : Type} (m : σ →₀ ℕ) (a : ℤ) :
    polyLength (monomial m a) = a.natAbs := by
  classical
  by_cases ha : a = 0 <;> simp [polyLength, support_monomial, ha]

private lemma polyLength_add {σ : Type} (p q : MvPolynomial σ ℤ) :
    polyLength (p + q) ≤ polyLength p + polyLength q := by
  simpa [Fin.sum_univ_two] using
    polyLength_sum_le Finset.univ ![p, q]

private lemma polyLength_mul {σ : Type} (p q : MvPolynomial σ ℤ) :
    polyLength (p * q) ≤ polyLength p * polyLength q := by
  classical
  conv_lhs => rw [p.as_sum, q.as_sum]
  simp only [Finset.sum_mul, Finset.mul_sum, monomial_mul]
  apply (polyLength_sum_le _ _).trans
  apply (Finset.sum_le_sum fun _ _ => polyLength_sum_le _ _).trans
  simp only [polyLength_monomial, Int.natAbs_mul]
  simp only [← Finset.mul_sum, ← Finset.sum_mul, ← polyLength_eq, le_refl]

private lemma polyLength_pow {σ : Type} (p : MvPolynomial σ ℤ) (n : ℕ) :
    polyLength (p ^ n) ≤ polyLength p ^ n := by
  induction n with
  | zero =>
    change polyLength (monomial (0 : σ →₀ ℕ) 1) ≤ 1
    exact (polyLength_monomial _ _).le
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact (polyLength_mul _ _).trans (Nat.mul_le_mul_right _ ih)

private lemma coeff_le_polyLength {σ : Type} (p : MvPolynomial σ ℤ) (m : σ →₀ ℕ) :
    (p.coeff m).natAbs ≤ polyLength p := by
  classical
  by_cases hm : m ∈ p.support
  · rw [polyLength_eq]
    exact Finset.single_le_sum (f := fun m => (p.coeff m).natAbs) (fun _ _ => Nat.zero_le _) hm
  · simp [notMem_support_iff.mp hm]

private lemma degree_neg (p : MvPolynomial (Fin 8) ℤ) :
    (-p).totalDegree = p.totalDegree := by simp [totalDegree]

private lemma jet_derivation_degree (i : Fin 8) :
    (ellipticJetDerivation (X i)).totalDegree ≤ 2 := by
  fin_cases i <;> simp [ellipticJetDerivation]
  have h₁ := totalDegree_mul (12 * X 5 : MvPolynomial (Fin 8) ℤ) (X 6)
  have h₂ := totalDegree_mul (C (12 : ℤ) : MvPolynomial (Fin 8) ℤ) (X 5)
  change (12 * X 5 : MvPolynomial (Fin 8) ℤ).totalDegree ≤ _ at h₂
  simp only [totalDegree_C, totalDegree_X] at h₁ h₂
  have hc : (12 : MvPolynomial (Fin 8) ℤ).totalDegree = 0 := totalDegree_C (12 : ℤ)
  omega

private lemma degree_sub (p q : MvPolynomial (Fin 8) ℤ) :
    (p - q).totalDegree ≤ max p.totalDegree q.totalDegree := by
  simpa [sub_eq_add_neg, degree_neg] using totalDegree_add p (-q)

private lemma cleared_polynomial_degree (M l₀ l₂ l₃ : ℕ)
    (h₂ : l₂ ≤ M) (h₃ : l₃ ≤ M) :
    (clearedAdditionPolynomial M l₀ l₂ l₃).totalDegree ≤ l₀ + 5 * M := by
  have hdiff (i j : Fin 8) : (X i - X j : MvPolynomial (Fin 8) ℤ).totalDegree ≤ 1 := by
    simpa using degree_sub (X i) (X j)
  have hsum (i j : Fin 8) : (X i + X j : MvPolynomial (Fin 8) ℤ).totalDegree ≤ 1 := by
    simpa using totalDegree_add (X i : MvPolynomial (Fin 8) ℤ) (X j)
  have hconst (a : ℤ) (p : MvPolynomial (Fin 8) ℤ) :
      (C a * p).totalDegree ≤ p.totalDegree := by
    simpa only [totalDegree_C, zero_add] using totalDegree_mul (C a) p
  have hA : (2 * (X 2 - X 5) : MvPolynomial (Fin 8) ℤ).totalDegree ≤ 1 :=
    (hconst 2 _).trans (hdiff 2 5)
  have hB : (-4 * (X 5 + X 2) * (X 2 - X 5) ^ 2 +
      (X 3 - X 6) ^ 2 : MvPolynomial (Fin 8) ℤ).totalDegree ≤ 3 := by
    apply (totalDegree_add _ _).trans
    apply max_le
    · have := totalDegree_mul (-4 * (X 5 + X 2) : MvPolynomial (Fin 8) ℤ)
        ((X 2 - X 5) ^ 2)
      have hc : (-4 * (X 5 + X 2) : MvPolynomial (Fin 8) ℤ).totalDegree ≤
          (X 5 + X 2 : MvPolynomial (Fin 8) ℤ).totalDegree := by
            simpa only [map_neg, map_ofNat] using hconst (-4) (X 5 + X 2)
      have hp := totalDegree_pow (X 2 - X 5 : MvPolynomial (Fin 8) ℤ) 2
      have := hsum 5 2
      have := hdiff 2 5
      omega
    · have := totalDegree_pow (X 3 - X 6 : MvPolynomial (Fin 8) ℤ) 2
      have := hdiff 3 6
      omega
  have hC : (2 * (X 4 + X 1) * (X 2 - X 5) + (X 3 - X 6) :
      MvPolynomial (Fin 8) ℤ).totalDegree ≤ 2 := by
    apply (totalDegree_add _ _).trans
    apply max_le
    · have := totalDegree_mul (2 * (X 4 + X 1) : MvPolynomial (Fin 8) ℤ) (X 2 - X 5)
      have hc : (2 * (X 4 + X 1) : MvPolynomial (Fin 8) ℤ).totalDegree ≤
          (X 4 + X 1 : MvPolynomial (Fin 8) ℤ).totalDegree := hconst 2 _
      have := hsum 4 1
      have := hdiff 2 5
      omega
    · exact (hdiff 3 6).trans (by omega)
  unfold clearedAdditionPolynomial
  apply (totalDegree_mul _ _).trans
  apply (Nat.add_le_add (totalDegree_mul _ _) (totalDegree_pow _ _)).trans
  apply (Nat.add_le_add (Nat.add_le_add (totalDegree_mul _ _) (totalDegree_pow _ _))
    (Nat.le_refl _)).trans
  rw [totalDegree_X_pow]
  have hp := totalDegree_pow (2 * (X 2 - X 5) : MvPolynomial (Fin 8) ℤ)
    (3 * M - 2 * l₂ - l₃)
  have hpa := Nat.mul_le_mul_left (3 * M - 2 * l₂ - l₃) hA
  have hpb := Nat.mul_le_mul_left l₂ hB
  have hpc := Nat.mul_le_mul_left l₃ hC
  omega


private lemma polyLength_C (a : ℤ) :
    polyLength (C a : MvPolynomial (Fin 8) ℤ) = a.natAbs :=
  polyLength_monomial 0 a

private lemma polyLength_X (i : Fin 8) :
    polyLength (X i : MvPolynomial (Fin 8) ℤ) = 1 :=
  polyLength_monomial _ 1

private lemma polyLength_neg (p : MvPolynomial (Fin 8) ℤ) :
    polyLength (-p) = polyLength p := by simp [polyLength]

private lemma length_mul_le {p q : MvPolynomial (Fin 8) ℤ} {a b : ℕ}
    (hp : polyLength p ≤ a) (hq : polyLength q ≤ b) :
    polyLength (p * q) ≤ a * b :=
  (polyLength_mul p q).trans (Nat.mul_le_mul hp hq)

private lemma length_pow_le {p : MvPolynomial (Fin 8) ℤ} {a : ℕ}
    (hp : polyLength p ≤ a) (n : ℕ) : polyLength (p ^ n) ≤ a ^ n :=
  (polyLength_pow p n).trans (Nat.pow_le_pow_left hp n)

private lemma jet_derivation_length (i : Fin 8) :
    polyLength (ellipticJetDerivation (X i)) ≤ 12 := by
  have h0 : polyLength (0 : MvPolynomial (Fin 8) ℤ) = 0 := by simpa using polyLength_C 0
  have h1 : polyLength (1 : MvPolynomial (Fin 8) ℤ) = 1 := polyLength_C 1
  fin_cases i <;> simp [ellipticJetDerivation, polyLength_X, polyLength_neg, h0, h1]
  simpa using length_mul_le
    (length_mul_le (polyLength_C 12).le (polyLength_X 5).le) (polyLength_X 6).le

private lemma cleared_polynomial_length (M l₀ l₂ l₃ : ℕ)
    (h₂ : l₂ ≤ M) (h₃ : l₃ ≤ M) :
    polyLength (clearedAdditionPolynomial M l₀ l₂ l₃) ≤ 23040 ^ M := by
  have hs (i j : Fin 8) : polyLength (X i + X j : MvPolynomial (Fin 8) ℤ) ≤ 2 := by
    simpa [polyLength_X] using polyLength_add (X i) (X j)
  have hd (i j : Fin 8) : polyLength (X i - X j : MvPolynomial (Fin 8) ℤ) ≤ 2 := by
    simpa [sub_eq_add_neg, polyLength_X, polyLength_neg] using polyLength_add (X i) (-X j)
  have hA : polyLength (2 * (X 2 - X 5) : MvPolynomial (Fin 8) ℤ) ≤ 4 :=
    length_mul_le (polyLength_C 2).le (hd 2 5)
  have hB : polyLength (-4 * (X 5 + X 2) * (X 2 - X 5) ^ 2 +
      (X 3 - X 6) ^ 2 : MvPolynomial (Fin 8) ℤ) ≤ 36 := by
    apply (polyLength_add _ _).trans
    have hc : polyLength (-4 : MvPolynomial (Fin 8) ℤ) ≤ 4 := by
      simpa using (polyLength_C (-4)).le
    exact Nat.add_le_add (length_mul_le (length_mul_le hc (hs 5 2))
      (length_pow_le (hd 2 5) 2)) (length_pow_le (hd 3 6) 2)
  have hC : polyLength (2 * (X 4 + X 1) * (X 2 - X 5) + (X 3 - X 6) :
      MvPolynomial (Fin 8) ℤ) ≤ 10 := by
    exact (polyLength_add _ _).trans (Nat.add_le_add
      (length_mul_le (length_mul_le (polyLength_C 2).le (hs 4 1)) (hd 2 5)) (hd 3 6))
  unfold clearedAdditionPolynomial
  calc
    _ ≤ 1 ^ l₀ * 4 ^ (3 * M - 2 * l₂ - l₃) * 36 ^ l₂ * 10 ^ l₃ :=
      length_mul_le (length_mul_le (length_mul_le
        (length_pow_le (polyLength_X 0).le l₀) (length_pow_le hA _))
        (length_pow_le hB _)) (length_pow_le hC _)
    _ ≤ 4 ^ (3 * M) * 36 ^ M * 10 ^ M := by
      simp only [one_pow, one_mul]
      gcongr <;> omega
    _ = _ := by rw [pow_mul, ← mul_pow, ← mul_pow]; norm_num

private theorem cleared_addition_height (M l₀ l₂ l₃ : ℕ)
    (h₂ : l₂ ≤ M) (h₃ : l₃ ≤ M) (n : ℕ) :
    (∑ m ∈ (ellipticJetDerivation^[n] (clearedAdditionPolynomial M l₀ l₂ l₃)).support,
      ((ellipticJetDerivation^[n] (clearedAdditionPolynomial M l₀ l₂ l₃)).coeff m).natAbs) ≤
      n.factorial * 2 ^ (41 * (l₀ + M + n)) := by
  have h := (TranscendenceTheory.polynomial_derivation_length_bound
    ellipticJetDerivation jet_derivation_degree 12 (by omega) jet_derivation_length
    (clearedAdditionPolynomial M l₀ l₂ l₃) n).2
  change polyLength _ ≤ _ at h ⊢
  have hlen := cleared_polynomial_length M l₀ l₂ l₃ h₂ h₃
  have hdeg := cleared_polynomial_degree M l₀ l₂ l₃ h₂ h₃
  apply h.trans
  change polyLength (clearedAdditionPolynomial M l₀ l₂ l₃) * n.factorial *
    24 ^ ((clearedAdditionPolynomial M l₀ l₂ l₃).totalDegree + n) ≤ _
  calc
    _ ≤ (2 ^ 16) ^ M * n.factorial * (2 ^ 5) ^ (l₀ + 5 * M + n) := by
      exact Nat.mul_le_mul
        (Nat.mul_le_mul_right _ (hlen.trans (Nat.pow_le_pow_left (by norm_num) M)))
        ((Nat.pow_le_pow_left (by norm_num : 24 ≤ 2 ^ 5) _).trans
          (Nat.pow_le_pow_right (by norm_num) (Nat.add_le_add_right hdeg n)))
    _ = n.factorial * 2 ^ (16 * M + 5 * (l₀ + 5 * M + n)) := by
      rw [← pow_mul, ← pow_mul, pow_add]
      ring
    _ ≤ _ := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by omega))

end WeierstrassEllipticZeta

open WeierstrassEllipticZeta
open scoped Polynomial

theorem solution
    (L : PeriodPair) (ω u₁ u₂ : ℂ)
    (h_grid : RegularAuxiliaryGridData L ω u₁ u₂)
    (h_zeta_deriv : ∀ z : ℂ, z ∉ L.lattice →
      HasDerivAt (weierstrassZeta L) (-L.weierstrassP z) z)
    (h_zeta_addition : ∀ z v : ℂ,
      z ∉ L.lattice → v ∉ L.lattice → z + v ∉ L.lattice →
      2 * (L.weierstrassP v - L.weierstrassP z) * weierstrassZeta L (z + v) =
        2 * (weierstrassZeta L z + weierstrassZeta L v) *
          (L.weierstrassP v - L.weierstrassP z) +
        L.derivWeierstrassP v - L.derivWeierstrassP z)
    (h_wp_addition : ∀ z v : ℂ,
      z ∉ L.lattice → v ∉ L.lattice → z + v ∉ L.lattice →
      4 * (L.weierstrassP v - L.weierstrassP z) ^ 2 * L.weierstrassP (z + v) =
        -4 * (L.weierstrassP z + L.weierstrassP v) *
          (L.weierstrassP v - L.weierstrassP z) ^ 2 +
        (L.derivWeierstrassP v - L.derivWeierstrassP z) ^ 2)
    (h_jets : ClearedAdditionJetData L)
    (θ : ℂ) (hθ : Transcendental ℚ θ)
    (ν : ℂ)
    (g : ℤ[X][X]) (hg_monic : g.Monic) (hg_degree : 0 < g.natDegree)
    (hg_kernel : ∀ p : ℤ[X][X],
      p.eval₂ (Polynomial.aeval θ).toRingHom ν = 0 ↔ g ∣ p)
    (d : ℤ[X]) (hd : Polynomial.aeval θ d ≠ 0)
    (h_data : ∀ i : Fin 18, ∃ p : ℤ[X][X],
      p.natDegree < g.natDegree ∧
      p.eval₂ (Polynomial.aeval θ).toRingHom ν = Polynomial.aeval θ d *
        (![L.g₂/4, L.g₃/4, ω, zetaQuasiPeriod L ω, u₁/2, u₂,
        weierstrassZeta L (u₁/2), L.weierstrassP (u₁/2),
        L.derivWeierstrassP (u₁/2), deriv L.derivWeierstrassP (u₁/2),
        L.weierstrassP u₁, L.derivWeierstrassP u₁, deriv L.derivWeierstrassP u₁,
        weierstrassZeta L u₁, L.weierstrassP u₂, L.derivWeierstrassP u₂,
        deriv L.derivWeierstrassP u₂, weierstrassZeta L u₂] i)) :
    ∃ a c : ℝ, 0 < a ∧ 0 < c ∧
      ∀ᶠ N : ℕ in Filter.atTop,
        ∃ S : TranscendenceTheory.ComplexAuxiliarySystem
          θ ν a ((3 + ‖θ‖ + ‖ν‖) * a) c N,
          S.yDegree < g.natDegree := by
  have h_jet_height := cleared_addition_height
  exact exists_complex_auxiliary_systems_from_bounded_polynomial_jets L ω u₁ u₂ h_grid
    h_zeta_deriv h_zeta_addition h_wp_addition h_jets h_jet_height θ hθ ν g hg_monic
    hg_degree hg_kernel d hd h_data
