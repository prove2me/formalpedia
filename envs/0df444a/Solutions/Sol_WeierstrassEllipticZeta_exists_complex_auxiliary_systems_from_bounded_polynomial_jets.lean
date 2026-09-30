-- Prove2me | solution 1 for WeierstrassEllipticZeta.exists_complex_auxiliary_systems_from_bounded_polynomial_jets
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-07T11:57:49.042341+00:00
-- url     : https://prove2.me/submissions/9bd641b2-db74-4597-9677-6bfd1ba95825

import Definitions.Def_WeierstrassEllipticZeta_ArithmeticJets
import Theorems.Thm_TranscendenceTheory_polynomial_clear_denominators_bound
import Theorems.Thm_WeierstrassEllipticZeta_exists_complex_auxiliary_systems_from_arithmetic_jets
import Mathlib.Tactic.FinCases

noncomputable section

open MvPolynomial

namespace WeierstrassEllipticZeta

private lemma pderiv_degreeOf_le {σ : Type} (p : MvPolynomial σ ℤ) (i j : σ) :
    (pderiv j p).degreeOf i ≤ p.degreeOf i := by
  classical
  rw [degreeOf_eq_sup]
  apply Finset.sup_le
  intro m hm
  have hc : p.coeff (m + Finsupp.single j 1) ≠ 0 := by
    have := mem_support_iff.mp hm
    rw [coeff_pderiv] at this
    exact (mul_ne_zero_iff.mp this).1
  have := monomial_le_degreeOf i (mem_support_iff.mpr hc)
  simp only [Finsupp.add_apply] at this
  omega

private lemma derivation_sum_apply {σ : Type} [Fintype σ]
    (F : σ → Derivation ℤ (MvPolynomial σ ℤ) (MvPolynomial σ ℤ))
    (p : MvPolynomial σ ℤ) : (∑ i, F i) p = ∑ i, F i p := by
  change (Derivation.coeFnAddMonoidHom (∑ i, F i)) p = _
  rw [map_sum, Finset.sum_apply]
  rfl

private lemma derivation_degreeOf_le {σ : Type} [Fintype σ]
    (D : Derivation ℤ (MvPolynomial σ ℤ) (MvPolynomial σ ℤ))
    (i : σ) (hD : ∀ j, (D (X j)).degreeOf i = 0) (p : MvPolynomial σ ℤ) :
    (D p).degreeOf i ≤ p.degreeOf i := by
  classical
  have hrepr : D = ∑ j, D (X j) • pderiv j := by
    apply MvPolynomial.derivation_ext
    intro j
    simp [derivation_sum_apply, Derivation.smul_apply, Pi.single_apply]
  have hvalue : D p = ∑ j, D (X j) * pderiv j p := by
    conv_lhs => rw [hrepr]
    simp [derivation_sum_apply]
  rw [hvalue]
  apply (degreeOf_sum_le _ _ _).trans
  apply Finset.sup_le
  intro j _
  simpa only [hD j, zero_add] using
    (degreeOf_mul_le i (D (X j)) (pderiv j p)).trans
      (Nat.add_le_add_left (pderiv_degreeOf_le p i j) _)

private lemma jet_fixed_degree (i : Fin 8) (hi : i.val < 4)
    (p : MvPolynomial (Fin 8) ℤ) (n : ℕ) :
    (ellipticJetDerivation^[n] p).degreeOf i ≤ p.degreeOf i := by
  have hD (j : Fin 8) : (ellipticJetDerivation (X j)).degreeOf i = 0 := by
    have hi5 : i ≠ 5 := by intro h; subst i; norm_num at hi
    have hi6 : i ≠ 6 := by intro h; subst i; norm_num at hi
    have hi7 : i ≠ 7 := by intro h; subst i; norm_num at hi
    fin_cases j <;> simp [ellipticJetDerivation, degreeOf_X, hi5, hi6, hi7]
    apply Nat.eq_zero_of_le_zero
    have h := degreeOf_mul_le i (12 * X 5 : MvPolynomial (Fin 8) ℤ) (X 6)
    have h' := degreeOf_C_mul_le (X 5 : MvPolynomial (Fin 8) ℤ) i 12
    change (12 * X 5 : MvPolynomial (Fin 8) ℤ).degreeOf i ≤ _ at h'
    simp [degreeOf_X, hi5, hi6] at h h'
    omega
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact (derivation_degreeOf_le ellipticJetDerivation i hD _).trans ih

private lemma cleared_polynomial_degree_zero (M l₂ l₃ : ℕ) :
    (clearedAdditionPolynomial M 0 l₂ l₃).degreeOf 0 = 0 := by
  have hmul (p q : MvPolynomial (Fin 8) ℤ)
      (hp : p.degreeOf 0 = 0) (hq : q.degreeOf 0 = 0) : (p * q).degreeOf 0 = 0 := by
    apply Nat.eq_zero_of_le_zero
    simpa [hp, hq] using degreeOf_mul_le 0 p q
  have hadd (p q : MvPolynomial (Fin 8) ℤ)
      (hp : p.degreeOf 0 = 0) (hq : q.degreeOf 0 = 0) : (p + q).degreeOf 0 = 0 := by
    apply Nat.eq_zero_of_le_zero
    simpa [hp, hq] using degreeOf_add_le 0 p q
  have hneg (p : MvPolynomial (Fin 8) ℤ) (hp : p.degreeOf 0 = 0) :
      (-p).degreeOf 0 = 0 := by simpa [degreeOf_eq_sup] using hp
  have hpow (p : MvPolynomial (Fin 8) ℤ) (n : ℕ) (hp : p.degreeOf 0 = 0) :
      (p ^ n).degreeOf 0 = 0 := by
    apply Nat.eq_zero_of_le_zero
    simpa [hp] using degreeOf_pow_le 0 p n
  have h2 : (2 : MvPolynomial (Fin 8) ℤ).degreeOf 0 = 0 := degreeOf_C 2 0
  have h4 : (4 : MvPolynomial (Fin 8) ℤ).degreeOf 0 = 0 := degreeOf_C 4 0
  simp only [clearedAdditionPolynomial, pow_zero, one_mul, sub_eq_add_neg]
  have hx (i : Fin 8) (hi : i ≠ 0) : (X i : MvPolynomial (Fin 8) ℤ).degreeOf 0 = 0 := by
    simp [degreeOf_X, Ne.symm hi]
  have hd25 := hadd _ _ (hx 2 (by decide)) (hneg _ (hx 5 (by decide)))
  have hd36 := hadd _ _ (hx 3 (by decide)) (hneg _ (hx 6 (by decide)))
  have ha := hmul _ _ h2 hd25
  have hb := hadd _ _
    (hmul _ _ (hmul _ _ (hneg _ h4)
      (hadd _ _ (hx 5 (by decide)) (hx 2 (by decide)))) (hpow _ 2 hd25))
    (hpow _ 2 hd36)
  have hc := hadd _ _
    (hmul _ _ (hmul _ _ h2 (hadd _ _ (hx 4 (by decide)) (hx 1 (by decide)))) hd25) hd36
  exact hmul _ _ (hmul _ _ (hpow _ _ ha) (hpow _ _ hb)) (hpow _ _ hc)

private lemma jet_coordinate_degrees (L : PeriodPair) (h_jets : ClearedAdditionJetData L)
    (M L₀ l₀ l₂ l₃ n : ℕ) (h₀ : l₀ ≤ L₀) (h₂ : l₂ ≤ M) (h₃ : l₃ ≤ M) :
    ∀ i : Fin 8,
      (ellipticJetDerivation^[n] (clearedAdditionPolynomial M l₀ l₂ l₃)).degreeOf i ≤
        (![L₀, 5 * M, 5 * M, 5 * M,
          L₀ + 5 * M + n, L₀ + 5 * M + n, L₀ + 5 * M + n, L₀ + 5 * M + n] i) := by
  have hbase : (clearedAdditionPolynomial M 0 l₂ l₃).totalDegree ≤ 5 * M := by
    simpa using (h_jets M 0 l₂ l₃ h₂ h₃ 0).1
  have hrepr : clearedAdditionPolynomial M l₀ l₂ l₃ =
      X 0 ^ l₀ * clearedAdditionPolynomial M 0 l₂ l₃ := by
    simp [clearedAdditionPolynomial, mul_assoc]
  have hzero :
      (ellipticJetDerivation^[n] (clearedAdditionPolynomial M l₀ l₂ l₃)).degreeOf 0 ≤ L₀ := by
    apply (jet_fixed_degree 0 (by decide) _ n).trans
    rw [hrepr]
    apply (degreeOf_mul_le _ _ _).trans
    simpa [cleared_polynomial_degree_zero] using h₀
  have hfixed (i : Fin 8) (hi : i.val < 4) (hi0 : i ≠ 0) :
      (ellipticJetDerivation^[n] (clearedAdditionPolynomial M l₀ l₂ l₃)).degreeOf i ≤ 5 * M := by
    apply (jet_fixed_degree i hi _ n).trans
    rw [hrepr]
    apply (degreeOf_mul_le _ _ _).trans
    have hpow := degreeOf_pow_le i (X 0 : MvPolynomial (Fin 8) ℤ) l₀
    have hrest := (degreeOf_le_totalDegree (clearedAdditionPolynomial M 0 l₂ l₃) i).trans hbase
    simp [degreeOf_X, hi0] at hpow
    omega
  have hall (i : Fin 8) :
      (ellipticJetDerivation^[n] (clearedAdditionPolynomial M l₀ l₂ l₃)).degreeOf i ≤
        L₀ + 5 * M + n := by
    apply (degreeOf_le_totalDegree _ i).trans
    exact (h_jets M l₀ l₂ l₃ h₂ h₃ n).1.trans (by omega)
  intro i
  fin_cases i
  · exact hzero
  · exact hfixed 1 (by decide) (by decide)
  · exact hfixed 2 (by decide) (by decide)
  · exact hfixed 3 (by decide) (by decide)
  all_goals exact hall _

private theorem arithmetic_jets_of_polynomial_jets (L : PeriodPair)
    (h_jets : ClearedAdditionJetData L)
    (h_height : ∀ (M l₀ l₂ l₃ : ℕ), l₂ ≤ M → l₃ ≤ M → ∀ n : ℕ,
      (∑ m ∈ (ellipticJetDerivation^[n] (clearedAdditionPolynomial M l₀ l₂ l₃)).support,
        ((ellipticJetDerivation^[n] (clearedAdditionPolynomial M l₀ l₂ l₃)).coeff m).natAbs) ≤
        n.factorial * 2 ^ (41 * (l₀ + M + n))) : ArithmeticJetData L := by
  intro M L₀ l₀ l₂ l₃ n h₀ h₂ h₃ k s q d H hsdeg hqdeg hslen hqlen
  obtain ⟨r, hrdeg, hrlen, hreval⟩ :=
    TranscendenceTheory.polynomial_clear_denominators_bound (A := ℂ)
      (ellipticJetDerivation^[n] (clearedAdditionPolynomial M l₀ l₂ l₃))
      k d H s q (jet_coordinate_degrees L h_jets M L₀ l₀ l₂ l₃ n h₀ h₂ h₃)
      hsdeg hqdeg hslen hqlen
  refine ⟨r, hrdeg, hrlen.trans ?_, ?_⟩
  · apply Nat.mul_le_mul_right
    apply (h_height M l₀ l₂ l₃ h₂ h₃ n).trans
    apply Nat.mul_le_mul_left
    exact Nat.pow_le_pow_right (by omega) (by omega)
  · intro w v z hv hz hvz hvalues
    rw [(h_jets M l₀ l₂ l₃ h₂ h₃ n).2 v z hv hz hvz]
    exact hreval (eval₂Hom (Int.castRingHom ℂ) w) (ellipticJetCoordinates L v z) hvalues

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
    (h_jet_height : ∀ (M l₀ l₂ l₃ : ℕ), l₂ ≤ M → l₃ ≤ M → ∀ n : ℕ,
      (∑ m ∈ (ellipticJetDerivation^[n] (clearedAdditionPolynomial M l₀ l₂ l₃)).support,
        ((ellipticJetDerivation^[n] (clearedAdditionPolynomial M l₀ l₂ l₃)).coeff m).natAbs) ≤
        n.factorial * 2 ^ (41 * (l₀ + M + n)))
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
  have h_arithmetic := arithmetic_jets_of_polynomial_jets L h_jets h_jet_height
  exact exists_complex_auxiliary_systems_from_arithmetic_jets L ω u₁ u₂ h_grid
    h_zeta_deriv h_zeta_addition h_wp_addition h_arithmetic θ hθ ν g hg_monic
    hg_degree hg_kernel d hd h_data
