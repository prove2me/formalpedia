-- Prove2me | solution 1 for WeierstrassEllipticZeta.exists_complex_auxiliary_systems_on_regular_grids
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-07T11:18:53.14584+00:00
-- url     : https://prove2.me/submissions/c0e5cd3a-1f54-488b-a7e1-13c60fdd3004

import Definitions.Def_WeierstrassEllipticZeta_DifferentialPolynomials
import Theorems.Thm_TranscendenceTheory_polynomial_ode_iterated_deriv
import Theorems.Thm_WeierstrassEllipticZeta_exists_complex_auxiliary_systems_from_polynomial_jets
import Theorems.Thm_WeierstrassEllipticZeta_hasDerivAt_derivWeierstrassP
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases

noncomputable section

set_option maxHeartbeats 600000

open MvPolynomial Filter
open scoped Topology

namespace WeierstrassEllipticZeta

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

private lemma jet_coordinates_ode (L : PeriodPair)
    (hzeta : ∀ z : ℂ, z ∉ L.lattice → HasDerivAt (weierstrassZeta L)
      (-L.weierstrassP z) z)
    (v z : ℂ) (hz : z ∉ L.lattice) (i : Fin 8) :
    HasDerivAt (fun w => ellipticJetCoordinates L v w i)
      (eval₂ (Int.castRingHom ℂ) (ellipticJetCoordinates L v z)
        (ellipticJetDerivation (X i))) z := by
  have hP : HasDerivAt L.weierstrassP (L.derivWeierstrassP z) z := by
    simpa using (L.differentiableOn_weierstrassP.differentiableAt
      (L.isClosed_lattice.isOpen_compl.mem_nhds hz)).hasDerivAt
  have hD := hasDerivAt_derivWeierstrassP L z hz
  have hDD : HasDerivAt (deriv L.derivWeierstrassP)
      (12 * L.weierstrassP z * L.derivWeierstrassP z) z := by
    have heq : deriv L.derivWeierstrassP =ᶠ[𝓝 z]
        (fun w => 6 * L.weierstrassP w ^ 2 - L.g₂ / 2) := by
      filter_upwards [L.isClosed_lattice.isOpen_compl.mem_nhds hz] with w hw
      exact (hasDerivAt_derivWeierstrassP L w hw).deriv
    have hh := (((hP.pow 2).const_mul 6).sub_const (L.g₂ / 2)).congr_of_eventuallyEq heq
    exact hh.congr_deriv (by ring)
  fin_cases i
  · simpa [ellipticJetCoordinates, ellipticJetDerivation] using (hasDerivAt_id z).add_const v
  · simpa [ellipticJetCoordinates, ellipticJetDerivation] using
      hasDerivAt_const z (weierstrassZeta L v)
  · simpa [ellipticJetCoordinates, ellipticJetDerivation] using
      hasDerivAt_const z (L.weierstrassP v)
  · simpa [ellipticJetCoordinates, ellipticJetDerivation] using
      hasDerivAt_const z (L.derivWeierstrassP v)
  · simpa [ellipticJetCoordinates, ellipticJetDerivation] using hzeta z hz
  · simpa [ellipticJetCoordinates, ellipticJetDerivation] using hP
  · simpa [ellipticJetCoordinates, ellipticJetDerivation, hD.deriv] using hD
  · simpa [ellipticJetCoordinates, ellipticJetDerivation] using hDD

private lemma cleared_monomial_eq (L : PeriodPair) (M l₀ l₂ l₃ : ℕ)
    (h₂ : l₂ ≤ M) (h₃ : l₃ ≤ M) (v z : ℂ)
    (hZ : 2 * (L.weierstrassP v - L.weierstrassP z) * weierstrassZeta L (z + v) =
      2 * (weierstrassZeta L z + weierstrassZeta L v) *
        (L.weierstrassP v - L.weierstrassP z) + L.derivWeierstrassP v - L.derivWeierstrassP z)
    (hP : 4 * (L.weierstrassP v - L.weierstrassP z) ^ 2 * L.weierstrassP (z + v) =
      -4 * (L.weierstrassP z + L.weierstrassP v) *
        (L.weierstrassP v - L.weierstrassP z) ^ 2 +
        (L.derivWeierstrassP v - L.derivWeierstrassP z) ^ 2) :
    clearedAdditionMonomial L v M l₀ l₂ l₃ z =
      eval₂ (Int.castRingHom ℂ) (ellipticJetCoordinates L v z)
        (clearedAdditionPolynomial M l₀ l₂ l₃) := by
  simp only [clearedAdditionPolynomial, eval₂_mul, eval₂_pow, eval₂_add,
    eval₂_sub, eval₂_X, eval₂_ofNat, eval₂_neg, ellipticJetCoordinates]
  simp only [Matrix.cons_val, Fin.isValue]
  rw [show 2 * (weierstrassZeta L z + weierstrassZeta L v) *
      (L.weierstrassP v - L.weierstrassP z) + (L.derivWeierstrassP v - L.derivWeierstrassP z) =
      2 * (L.weierstrassP v - L.weierstrassP z) * weierstrassZeta L (z + v) by
        linear_combination -hZ]
  rw [← hP]
  have hnum : 4 * (L.weierstrassP v - L.weierstrassP z) ^ 2 =
      (2 * (L.weierstrassP v - L.weierstrassP z)) ^ 2 := by ring
  rw [hnum]
  have hpow : 3 * M = (3 * M - 2 * l₂ - l₃) + 2 * l₂ + l₃ := by omega
  unfold clearedAdditionMonomial
  conv_lhs => rw [hpow, pow_add, pow_add]
  simp only [mul_pow, ← pow_mul]
  ring

private theorem cleared_addition_jet_data (L : PeriodPair)
    (hzeta : ∀ z : ℂ, z ∉ L.lattice → HasDerivAt (weierstrassZeta L)
      (-L.weierstrassP z) z)
    (hZ : ∀ z v : ℂ, z ∉ L.lattice → v ∉ L.lattice → z + v ∉ L.lattice →
      2 * (L.weierstrassP v - L.weierstrassP z) * weierstrassZeta L (z + v) =
        2 * (weierstrassZeta L z + weierstrassZeta L v) *
          (L.weierstrassP v - L.weierstrassP z) + L.derivWeierstrassP v - L.derivWeierstrassP z)
    (hP : ∀ z v : ℂ, z ∉ L.lattice → v ∉ L.lattice → z + v ∉ L.lattice →
      4 * (L.weierstrassP v - L.weierstrassP z) ^ 2 * L.weierstrassP (z + v) =
        -4 * (L.weierstrassP z + L.weierstrassP v) *
          (L.weierstrassP v - L.weierstrassP z) ^ 2 +
          (L.derivWeierstrassP v - L.derivWeierstrassP z) ^ 2) :
    ClearedAdditionJetData L := by
  intro M l₀ l₂ l₃ h₂ h₃ n
  have hpoly := cleared_polynomial_degree M l₀ l₂ l₃ h₂ h₃
  have hjet (v : ℂ) := TranscendenceTheory.polynomial_ode_iterated_deriv
    ellipticJetDerivation jet_derivation_degree (L.lattice : Set ℂ)ᶜ
    L.isClosed_lattice.isOpen_compl (fun i w => ellipticJetCoordinates L v w i)
    (fun z hz i => jet_coordinates_ode L hzeta v z hz i)
    (clearedAdditionPolynomial M l₀ l₂ l₃) n
  refine ⟨(hjet 0).1.trans (by omega), ?_⟩
  intro v z hv hz hzv
  have heq : clearedAdditionMonomial L v M l₀ l₂ l₃ =ᶠ[𝓝 z]
      (fun w => eval₂ (Int.castRingHom ℂ) (ellipticJetCoordinates L v w)
        (clearedAdditionPolynomial M l₀ l₂ l₃)) := by
    have hnear : ∀ᶠ w in 𝓝 z, w + v ∉ L.lattice :=
      (continuousAt_id.add_const v).eventually
        (L.isClosed_lattice.isOpen_compl.mem_nhds hzv)
    filter_upwards [L.isClosed_lattice.isOpen_compl.mem_nhds hz, hnear] with w hw hwv
    exact cleared_monomial_eq L M l₀ l₂ l₃ h₂ h₃ v w
      (hZ w v hw hv hwv) (hP w v hw hv hwv)
  rw [heq.iteratedDeriv_eq]
  exact (hjet v).2 z hz

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
  have h_jets := cleared_addition_jet_data L h_zeta_deriv h_zeta_addition h_wp_addition
  exact exists_complex_auxiliary_systems_from_polynomial_jets L ω u₁ u₂ h_grid
    h_zeta_deriv h_zeta_addition h_wp_addition h_jets θ hθ ν g hg_monic hg_degree
    hg_kernel d hd h_data
