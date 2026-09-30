-- Prove2me | solution 1 for WeierstrassEllipticZeta.auxiliary_grid_jet_matrices_of_arithmetic_model
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-14T00:28:03.523982+00:00
-- url     : https://prove2.me/submissions/c9cbbddb-6cbd-4410-9aee-5d9b0d0478ed

import Definitions.Def_WeierstrassEllipticZeta_DifferentialPolynomials
import Theorems.Thm_TranscendenceTheory_polynomial_ode_iterated_deriv
import Theorems.Thm_WeierstrassEllipticZeta_hasDerivAt_derivWeierstrassP
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases
import Theorems.Thm_TranscendenceTheory_polynomial_derivation_length_bound
import Mathlib.Tactic.GCongr
import Definitions.Def_WeierstrassEllipticZeta_ArithmeticJets
import Theorems.Thm_TranscendenceTheory_polynomial_clear_denominators_bound
import Theorems.Thm_TranscendenceTheory_bivariate_monic_reduction_bound
import Definitions.Def_WeierstrassEllipticZeta_ReducedArithmeticJets
import Theorems.Thm_WeierstrassEllipticZeta_cleared_addition_jet_vanishing_iff
import Definitions.Def_WeierstrassEllipticZeta_ReducedJetSystems
import Theorems.Thm_WeierstrassEllipticZeta_period_translate_polynomial_jets
import Theorems.Thm_WeierstrassEllipticZeta_auxiliary_parameter_estimates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Theorems.Thm_WeierstrassEllipticZeta_hasDerivAt_weierstrassZeta
import Theorems.Thm_WeierstrassEllipticZeta_zeta_addition_formula
import Theorems.Thm_WeierstrassEllipticZeta_wp_addition_formula
import Theorems.Thm_WeierstrassEllipticZeta_auxiliary_nonlattice_coordinate_presentations
import Theorems.Thm_WeierstrassEllipticZeta_bounded_auxiliary_nonlattice_jet_systems
import Theorems.Thm_WeierstrassEllipticZeta_bounded_auxiliary_period_jet_systems
import Theorems.Thm_WeierstrassEllipticZeta_assemble_auxiliary_grid_jet_matrices
import Definitions.Def_WeierstrassEllipticZeta_GridJetMatrices
import Definitions.Def_WeierstrassEllipticZeta_AuxiliaryParameters
import Mathlib.RingTheory.Algebraic.Defs

-- Closed construction helpers extracted from Sol_WeierstrassEllipticZeta_exists_complex_auxiliary_systems_on_regular_grids.lean
noncomputable section

set_option maxHeartbeats 600000

open MvPolynomial Filter
open scoped Topology

namespace WeierstrassEllipticZeta

private lemma p2mL8_0_degree_neg (p : MvPolynomial (Fin 8) ℤ) :
    (-p).totalDegree = p.totalDegree := by simp [totalDegree]

private lemma p2mL8_0_jet_derivation_degree (i : Fin 8) :
    (ellipticJetDerivation (X i)).totalDegree ≤ 2 := by
  fin_cases i <;> simp [ellipticJetDerivation]
  have h₁ := totalDegree_mul (12 * X 5 : MvPolynomial (Fin 8) ℤ) (X 6)
  have h₂ := totalDegree_mul (C (12 : ℤ) : MvPolynomial (Fin 8) ℤ) (X 5)
  change (12 * X 5 : MvPolynomial (Fin 8) ℤ).totalDegree ≤ _ at h₂
  simp only [totalDegree_C, totalDegree_X] at h₁ h₂
  have hc : (12 : MvPolynomial (Fin 8) ℤ).totalDegree = 0 := totalDegree_C (12 : ℤ)
  omega

private lemma p2mL8_0_degree_sub (p q : MvPolynomial (Fin 8) ℤ) :
    (p - q).totalDegree ≤ max p.totalDegree q.totalDegree := by
  simpa [sub_eq_add_neg, p2mL8_0_degree_neg] using totalDegree_add p (-q)

private lemma p2mL8_0_cleared_polynomial_degree (M l₀ l₂ l₃ : ℕ)
    (h₂ : l₂ ≤ M) (h₃ : l₃ ≤ M) :
    (clearedAdditionPolynomial M l₀ l₂ l₃).totalDegree ≤ l₀ + 5 * M := by
  have hdiff (i j : Fin 8) : (X i - X j : MvPolynomial (Fin 8) ℤ).totalDegree ≤ 1 := by
    simpa using p2mL8_0_degree_sub (X i) (X j)
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

private lemma p2mL8_0_jet_coordinates_ode (L : PeriodPair)
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

private lemma p2mL8_0_cleared_monomial_eq (L : PeriodPair) (M l₀ l₂ l₃ : ℕ)
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

private theorem p2mL8_0_cleared_addition_jet_data (L : PeriodPair)
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
  have hpoly := p2mL8_0_cleared_polynomial_degree M l₀ l₂ l₃ h₂ h₃
  have hjet (v : ℂ) := TranscendenceTheory.polynomial_ode_iterated_deriv
    ellipticJetDerivation p2mL8_0_jet_derivation_degree (L.lattice : Set ℂ)ᶜ
    L.isClosed_lattice.isOpen_compl (fun i w => ellipticJetCoordinates L v w i)
    (fun z hz i => p2mL8_0_jet_coordinates_ode L hzeta v z hz i)
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
    exact p2mL8_0_cleared_monomial_eq L M l₀ l₂ l₃ h₂ h₃ v w
      (hZ w v hw hv hwv) (hP w v hw hv hwv)
  rw [heq.iteratedDeriv_eq]
  exact (hjet v).2 z hz

end WeierstrassEllipticZeta

open WeierstrassEllipticZeta
open scoped Polynomial

-- Closed construction helpers extracted from Sol_WeierstrassEllipticZeta_exists_complex_auxiliary_systems_from_polynomial_jets.lean
noncomputable section

open MvPolynomial

namespace WeierstrassEllipticZeta

private def p2mL8_1_polyLength {σ : Type} (p : MvPolynomial σ ℤ) : ℕ :=
  ∑ m ∈ p.support, (p.coeff m).natAbs

private lemma p2mL8_1_polyLength_eq {σ : Type} (p : MvPolynomial σ ℤ) :
    p2mL8_1_polyLength p = ∑ m ∈ p.support, (p.coeff m).natAbs := rfl

private lemma p2mL8_1_polyLength_sum_le {σ ι : Type} (s : Finset ι)
    (f : ι → MvPolynomial σ ℤ) :
    p2mL8_1_polyLength (∑ i ∈ s, f i) ≤ ∑ i ∈ s, p2mL8_1_polyLength (f i) := by
  classical
  let t := s.biUnion fun i => (f i).support
  have heq (p : MvPolynomial σ ℤ) (hp : p.support ⊆ t) :
      p2mL8_1_polyLength p = ∑ m ∈ t, (p.coeff m).natAbs := by
    rw [p2mL8_1_polyLength_eq]
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
    _ = ∑ i ∈ s, p2mL8_1_polyLength (f i) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      exact (heq _ (Finset.subset_biUnion_of_mem (fun i => (f i).support) hi)).symm

private lemma p2mL8_1_polyLength_monomial {σ : Type} (m : σ →₀ ℕ) (a : ℤ) :
    p2mL8_1_polyLength (monomial m a) = a.natAbs := by
  classical
  by_cases ha : a = 0 <;> simp [p2mL8_1_polyLength, support_monomial, ha]

private lemma p2mL8_1_polyLength_add {σ : Type} (p q : MvPolynomial σ ℤ) :
    p2mL8_1_polyLength (p + q) ≤ p2mL8_1_polyLength p + p2mL8_1_polyLength q := by
  simpa [Fin.sum_univ_two] using
    p2mL8_1_polyLength_sum_le Finset.univ ![p, q]

private lemma p2mL8_1_polyLength_mul {σ : Type} (p q : MvPolynomial σ ℤ) :
    p2mL8_1_polyLength (p * q) ≤ p2mL8_1_polyLength p * p2mL8_1_polyLength q := by
  classical
  conv_lhs => rw [p.as_sum, q.as_sum]
  simp only [Finset.sum_mul, Finset.mul_sum, monomial_mul]
  apply (p2mL8_1_polyLength_sum_le _ _).trans
  apply (Finset.sum_le_sum fun _ _ => p2mL8_1_polyLength_sum_le _ _).trans
  simp only [p2mL8_1_polyLength_monomial, Int.natAbs_mul]
  simp only [← Finset.mul_sum, ← Finset.sum_mul, ← p2mL8_1_polyLength_eq, le_refl]

private lemma p2mL8_1_polyLength_pow {σ : Type} (p : MvPolynomial σ ℤ) (n : ℕ) :
    p2mL8_1_polyLength (p ^ n) ≤ p2mL8_1_polyLength p ^ n := by
  induction n with
  | zero =>
    change p2mL8_1_polyLength (monomial (0 : σ →₀ ℕ) 1) ≤ 1
    exact (p2mL8_1_polyLength_monomial _ _).le
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact (p2mL8_1_polyLength_mul _ _).trans (Nat.mul_le_mul_right _ ih)

private lemma p2mL8_1_coeff_le_polyLength {σ : Type} (p : MvPolynomial σ ℤ) (m : σ →₀ ℕ) :
    (p.coeff m).natAbs ≤ p2mL8_1_polyLength p := by
  classical
  by_cases hm : m ∈ p.support
  · rw [p2mL8_1_polyLength_eq]
    exact Finset.single_le_sum (f := fun m => (p.coeff m).natAbs) (fun _ _ => Nat.zero_le _) hm
  · simp [notMem_support_iff.mp hm]

private lemma p2mL8_1_degree_neg (p : MvPolynomial (Fin 8) ℤ) :
    (-p).totalDegree = p.totalDegree := by simp [totalDegree]

private lemma p2mL8_1_jet_derivation_degree (i : Fin 8) :
    (ellipticJetDerivation (X i)).totalDegree ≤ 2 := by
  fin_cases i <;> simp [ellipticJetDerivation]
  have h₁ := totalDegree_mul (12 * X 5 : MvPolynomial (Fin 8) ℤ) (X 6)
  have h₂ := totalDegree_mul (C (12 : ℤ) : MvPolynomial (Fin 8) ℤ) (X 5)
  change (12 * X 5 : MvPolynomial (Fin 8) ℤ).totalDegree ≤ _ at h₂
  simp only [totalDegree_C, totalDegree_X] at h₁ h₂
  have hc : (12 : MvPolynomial (Fin 8) ℤ).totalDegree = 0 := totalDegree_C (12 : ℤ)
  omega

private lemma p2mL8_1_degree_sub (p q : MvPolynomial (Fin 8) ℤ) :
    (p - q).totalDegree ≤ max p.totalDegree q.totalDegree := by
  simpa [sub_eq_add_neg, p2mL8_1_degree_neg] using totalDegree_add p (-q)

private lemma p2mL8_1_cleared_polynomial_degree (M l₀ l₂ l₃ : ℕ)
    (h₂ : l₂ ≤ M) (h₃ : l₃ ≤ M) :
    (clearedAdditionPolynomial M l₀ l₂ l₃).totalDegree ≤ l₀ + 5 * M := by
  have hdiff (i j : Fin 8) : (X i - X j : MvPolynomial (Fin 8) ℤ).totalDegree ≤ 1 := by
    simpa using p2mL8_1_degree_sub (X i) (X j)
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


private lemma p2mL8_1_polyLength_C (a : ℤ) :
    p2mL8_1_polyLength (C a : MvPolynomial (Fin 8) ℤ) = a.natAbs :=
  p2mL8_1_polyLength_monomial 0 a

private lemma p2mL8_1_polyLength_X (i : Fin 8) :
    p2mL8_1_polyLength (X i : MvPolynomial (Fin 8) ℤ) = 1 :=
  p2mL8_1_polyLength_monomial _ 1

private lemma p2mL8_1_polyLength_neg (p : MvPolynomial (Fin 8) ℤ) :
    p2mL8_1_polyLength (-p) = p2mL8_1_polyLength p := by simp [p2mL8_1_polyLength]

private lemma p2mL8_1_length_mul_le {p q : MvPolynomial (Fin 8) ℤ} {a b : ℕ}
    (hp : p2mL8_1_polyLength p ≤ a) (hq : p2mL8_1_polyLength q ≤ b) :
    p2mL8_1_polyLength (p * q) ≤ a * b :=
  (p2mL8_1_polyLength_mul p q).trans (Nat.mul_le_mul hp hq)

private lemma p2mL8_1_length_pow_le {p : MvPolynomial (Fin 8) ℤ} {a : ℕ}
    (hp : p2mL8_1_polyLength p ≤ a) (n : ℕ) : p2mL8_1_polyLength (p ^ n) ≤ a ^ n :=
  (p2mL8_1_polyLength_pow p n).trans (Nat.pow_le_pow_left hp n)

private lemma p2mL8_1_jet_derivation_length (i : Fin 8) :
    p2mL8_1_polyLength (ellipticJetDerivation (X i)) ≤ 12 := by
  have h0 : p2mL8_1_polyLength (0 : MvPolynomial (Fin 8) ℤ) = 0 := by simpa using p2mL8_1_polyLength_C 0
  have h1 : p2mL8_1_polyLength (1 : MvPolynomial (Fin 8) ℤ) = 1 := p2mL8_1_polyLength_C 1
  fin_cases i <;> simp [ellipticJetDerivation, p2mL8_1_polyLength_X, p2mL8_1_polyLength_neg, h0, h1]
  simpa using p2mL8_1_length_mul_le
    (p2mL8_1_length_mul_le (p2mL8_1_polyLength_C 12).le (p2mL8_1_polyLength_X 5).le) (p2mL8_1_polyLength_X 6).le

private lemma p2mL8_1_cleared_polynomial_length (M l₀ l₂ l₃ : ℕ)
    (h₂ : l₂ ≤ M) (h₃ : l₃ ≤ M) :
    p2mL8_1_polyLength (clearedAdditionPolynomial M l₀ l₂ l₃) ≤ 23040 ^ M := by
  have hs (i j : Fin 8) : p2mL8_1_polyLength (X i + X j : MvPolynomial (Fin 8) ℤ) ≤ 2 := by
    simpa [p2mL8_1_polyLength_X] using p2mL8_1_polyLength_add (X i) (X j)
  have hd (i j : Fin 8) : p2mL8_1_polyLength (X i - X j : MvPolynomial (Fin 8) ℤ) ≤ 2 := by
    simpa [sub_eq_add_neg, p2mL8_1_polyLength_X, p2mL8_1_polyLength_neg] using p2mL8_1_polyLength_add (X i) (-X j)
  have hA : p2mL8_1_polyLength (2 * (X 2 - X 5) : MvPolynomial (Fin 8) ℤ) ≤ 4 :=
    p2mL8_1_length_mul_le (p2mL8_1_polyLength_C 2).le (hd 2 5)
  have hB : p2mL8_1_polyLength (-4 * (X 5 + X 2) * (X 2 - X 5) ^ 2 +
      (X 3 - X 6) ^ 2 : MvPolynomial (Fin 8) ℤ) ≤ 36 := by
    apply (p2mL8_1_polyLength_add _ _).trans
    have hc : p2mL8_1_polyLength (-4 : MvPolynomial (Fin 8) ℤ) ≤ 4 := by
      simpa using (p2mL8_1_polyLength_C (-4)).le
    exact Nat.add_le_add (p2mL8_1_length_mul_le (p2mL8_1_length_mul_le hc (hs 5 2))
      (p2mL8_1_length_pow_le (hd 2 5) 2)) (p2mL8_1_length_pow_le (hd 3 6) 2)
  have hC : p2mL8_1_polyLength (2 * (X 4 + X 1) * (X 2 - X 5) + (X 3 - X 6) :
      MvPolynomial (Fin 8) ℤ) ≤ 10 := by
    exact (p2mL8_1_polyLength_add _ _).trans (Nat.add_le_add
      (p2mL8_1_length_mul_le (p2mL8_1_length_mul_le (p2mL8_1_polyLength_C 2).le (hs 4 1)) (hd 2 5)) (hd 3 6))
  unfold clearedAdditionPolynomial
  calc
    _ ≤ 1 ^ l₀ * 4 ^ (3 * M - 2 * l₂ - l₃) * 36 ^ l₂ * 10 ^ l₃ :=
      p2mL8_1_length_mul_le (p2mL8_1_length_mul_le (p2mL8_1_length_mul_le
        (p2mL8_1_length_pow_le (p2mL8_1_polyLength_X 0).le l₀) (p2mL8_1_length_pow_le hA _))
        (p2mL8_1_length_pow_le hB _)) (p2mL8_1_length_pow_le hC _)
    _ ≤ 4 ^ (3 * M) * 36 ^ M * 10 ^ M := by
      simp only [one_pow, one_mul]
      gcongr <;> omega
    _ = _ := by rw [pow_mul, ← mul_pow, ← mul_pow]; norm_num

private theorem p2mL8_1_cleared_addition_height (M l₀ l₂ l₃ : ℕ)
    (h₂ : l₂ ≤ M) (h₃ : l₃ ≤ M) (n : ℕ) :
    (∑ m ∈ (ellipticJetDerivation^[n] (clearedAdditionPolynomial M l₀ l₂ l₃)).support,
      ((ellipticJetDerivation^[n] (clearedAdditionPolynomial M l₀ l₂ l₃)).coeff m).natAbs) ≤
      n.factorial * 2 ^ (41 * (l₀ + M + n)) := by
  have h := (TranscendenceTheory.polynomial_derivation_length_bound
    ellipticJetDerivation p2mL8_1_jet_derivation_degree 12 (by omega) p2mL8_1_jet_derivation_length
    (clearedAdditionPolynomial M l₀ l₂ l₃) n).2
  change p2mL8_1_polyLength _ ≤ _ at h ⊢
  have hlen := p2mL8_1_cleared_polynomial_length M l₀ l₂ l₃ h₂ h₃
  have hdeg := p2mL8_1_cleared_polynomial_degree M l₀ l₂ l₃ h₂ h₃
  apply h.trans
  change p2mL8_1_polyLength (clearedAdditionPolynomial M l₀ l₂ l₃) * n.factorial *
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

-- Closed construction helpers extracted from Sol_WeierstrassEllipticZeta_exists_complex_auxiliary_systems_from_bounded_polynomial_jets.lean
noncomputable section

open MvPolynomial

namespace WeierstrassEllipticZeta

private lemma p2mL8_2_pderiv_degreeOf_le {σ : Type} (p : MvPolynomial σ ℤ) (i j : σ) :
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

private lemma p2mL8_2_derivation_sum_apply {σ : Type} [Fintype σ]
    (F : σ → Derivation ℤ (MvPolynomial σ ℤ) (MvPolynomial σ ℤ))
    (p : MvPolynomial σ ℤ) : (∑ i, F i) p = ∑ i, F i p := by
  change (Derivation.coeFnAddMonoidHom (∑ i, F i)) p = _
  rw [map_sum, Finset.sum_apply]
  rfl

private lemma p2mL8_2_derivation_degreeOf_le {σ : Type} [Fintype σ]
    (D : Derivation ℤ (MvPolynomial σ ℤ) (MvPolynomial σ ℤ))
    (i : σ) (hD : ∀ j, (D (X j)).degreeOf i = 0) (p : MvPolynomial σ ℤ) :
    (D p).degreeOf i ≤ p.degreeOf i := by
  classical
  have hrepr : D = ∑ j, D (X j) • pderiv j := by
    apply MvPolynomial.derivation_ext
    intro j
    simp [p2mL8_2_derivation_sum_apply, Derivation.smul_apply, Pi.single_apply]
  have hvalue : D p = ∑ j, D (X j) * pderiv j p := by
    conv_lhs => rw [hrepr]
    simp [p2mL8_2_derivation_sum_apply]
  rw [hvalue]
  apply (degreeOf_sum_le _ _ _).trans
  apply Finset.sup_le
  intro j _
  simpa only [hD j, zero_add] using
    (degreeOf_mul_le i (D (X j)) (pderiv j p)).trans
      (Nat.add_le_add_left (p2mL8_2_pderiv_degreeOf_le p i j) _)

private lemma p2mL8_2_jet_fixed_degree (i : Fin 8) (hi : i.val < 4)
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
    exact (p2mL8_2_derivation_degreeOf_le ellipticJetDerivation i hD _).trans ih

private lemma p2mL8_2_cleared_polynomial_degree_zero (M l₂ l₃ : ℕ) :
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

private lemma p2mL8_2_jet_coordinate_degrees (L : PeriodPair) (h_jets : ClearedAdditionJetData L)
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
    apply (p2mL8_2_jet_fixed_degree 0 (by decide) _ n).trans
    rw [hrepr]
    apply (degreeOf_mul_le _ _ _).trans
    simpa [p2mL8_2_cleared_polynomial_degree_zero] using h₀
  have hfixed (i : Fin 8) (hi : i.val < 4) (hi0 : i ≠ 0) :
      (ellipticJetDerivation^[n] (clearedAdditionPolynomial M l₀ l₂ l₃)).degreeOf i ≤ 5 * M := by
    apply (p2mL8_2_jet_fixed_degree i hi _ n).trans
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

private theorem p2mL8_2_arithmetic_jets_of_polynomial_jets (L : PeriodPair)
    (h_jets : ClearedAdditionJetData L)
    (h_height : ∀ (M l₀ l₂ l₃ : ℕ), l₂ ≤ M → l₃ ≤ M → ∀ n : ℕ,
      (∑ m ∈ (ellipticJetDerivation^[n] (clearedAdditionPolynomial M l₀ l₂ l₃)).support,
        ((ellipticJetDerivation^[n] (clearedAdditionPolynomial M l₀ l₂ l₃)).coeff m).natAbs) ≤
        n.factorial * 2 ^ (41 * (l₀ + M + n))) : ArithmeticJetData L := by
  intro M L₀ l₀ l₂ l₃ n h₀ h₂ h₃ k s q d H hsdeg hqdeg hslen hqlen
  obtain ⟨r, hrdeg, hrlen, hreval⟩ :=
    TranscendenceTheory.polynomial_clear_denominators_bound (A := ℂ)
      (ellipticJetDerivation^[n] (clearedAdditionPolynomial M l₀ l₂ l₃))
      k d H s q (p2mL8_2_jet_coordinate_degrees L h_jets M L₀ l₀ l₂ l₃ n h₀ h₂ h₃)
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

-- Closed construction helpers extracted from Sol_WeierstrassEllipticZeta_exists_complex_auxiliary_systems_from_arithmetic_jets.lean
noncomputable section

open scoped Polynomial

namespace WeierstrassEllipticZeta

private theorem p2mL8_3_reduced_arithmetic_jets_of_arithmetic_jets (L : PeriodPair)
    (h_arithmetic : ArithmeticJetData L) (θ ν : ℂ)
    (g : ℤ[X][X]) (hg : g.Monic) (hg_degree : 0 < g.natDegree)
    (hg_zero : g.eval₂ (Polynomial.aeval θ).toRingHom ν = 0) :
    ReducedArithmeticJetData L θ ν g := by
  classical
  let B := g.support.sup fun i => (g.coeff i).natDegree
  let H := 1 + ∑ i ∈ g.support, ∑ j ∈ (g.coeff i).support,
    ((g.coeff i).coeff j).natAbs
  have hB (i : ℕ) : (g.coeff i).natDegree ≤ B := by
    by_cases hi : i ∈ g.support
    · exact Finset.le_sup (f := fun i => (g.coeff i).natDegree) hi
    · simp [Polynomial.notMem_support_iff.mp hi]
  refine ⟨B + 1, H, by omega, by dsimp [H]; omega, ?_⟩
  intro M L₀ l₀ l₂ l₃ n hl₀ hl₂ hl₃
  dsimp only
  intro s q d h hsdeg hqdeg hslen hqlen
  obtain ⟨p, hpdeg, hplen, hpeval⟩ :=
    h_arithmetic M L₀ l₀ l₂ l₃ n hl₀ hl₂ hl₃ s q d h hsdeg hqdeg hslen hqlen
  obtain ⟨r, hrY, hrX, hrlen, hreval⟩ :=
    TranscendenceTheory.bivariate_monic_reduction_bound g hg hg_degree B hB p
  refine ⟨r, hrY, ?_, ?_, ?_⟩
  · intro j
    exact (hrX j).trans (Nat.mul_le_mul_left _ hpdeg)
  · apply hrlen.trans
    exact Nat.mul_le_mul hplen (Nat.pow_le_pow_right (by omega)
      (Nat.add_le_add_right hpdeg 1))
  · intro v z hv hz hzv hcoord
    have heval := hreval ℂ (Polynomial.aeval θ).toRingHom ν hg_zero
    simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
      Polynomial.aeval_X] at heval
    exact heval.trans (hpeval ![θ, ν] v z hv hz hzv hcoord)

end WeierstrassEllipticZeta

open WeierstrassEllipticZeta

-- Closed construction helpers extracted from Sol_WeierstrassEllipticZeta_exists_complex_auxiliary_systems_from_reduced_arithmetic_jets.lean
noncomputable section

open scoped Polynomial

namespace WeierstrassEllipticZeta

private theorem p2mL8_4_reduced_jet_systems_of_reduced_jets
    (L : PeriodPair)
    (hzeta : ∀ z : ℂ, z ∉ L.lattice →
      HasDerivAt (weierstrassZeta L) (-L.weierstrassP z) z)
    (hadd : ∀ z v : ℂ,
      z ∉ L.lattice → v ∉ L.lattice → z + v ∉ L.lattice →
      2 * (L.weierstrassP v - L.weierstrassP z) * weierstrassZeta L (z + v) =
        2 * (weierstrassZeta L z + weierstrassZeta L v) *
          (L.weierstrassP v - L.weierstrassP z) +
        L.derivWeierstrassP v - L.derivWeierstrassP z)
    (θ ν : ℂ) (g : ℤ[X][X]) (h_reduced : ReducedArithmeticJetData L θ ν g) :
    ReducedArithmeticJetSystemData L θ ν g := by
  classical
  obtain ⟨B, H, hB, hH, h_reduced⟩ := h_reduced
  refine ⟨B, H, hB, hH, ?_⟩
  intro M L₀ T
  dsimp only
  intro s q d h hs hq hsH hqH
  let I := Fin (L₀ + 1) × Fin (M + 1) × Fin (M + 1)
  let k : ℕ → Fin 8 → ℕ := fun n =>
    ![L₀, 5 * M, 5 * M, 5 * M,
      L₀ + 5 * M + n, L₀ + 5 * M + n, L₀ + 5 * M + n, L₀ + 5 * M + n]
  have hall (n : Fin T) (i : I) := h_reduced M L₀ i.1 i.2.1 i.2.2 n
    (Nat.le_of_lt_succ i.1.isLt) (Nat.le_of_lt_succ i.2.1.isLt)
    (Nat.le_of_lt_succ i.2.2.isLt) s q d h hs hq hsH hqH
  choose R hRy hRx hRH hReval using hall
  refine ⟨R, fun n i => ⟨hRy n i, hRx n i, hRH n i⟩, ?_⟩
  intro v z hv hz hp hcoord
  have heval := fun n i => hReval n i v z hv hz hp hcoord
  refine ⟨heval, ?_⟩
  intro hm hnonzero c
  have hcancel := (cleared_addition_jet_vanishing_iff L hzeta hadd z v hz hv hp hm
    M T (fun i : I => i.1.val) (fun i : I => i.2.1.val)
      (fun i : I => i.2.2.val) c).2
  let Q : Fin T → ℂ := fun n =>
    ∏ a, MvPolynomial.eval₂ (Int.castRingHom ℂ) ![θ, ν] (q a) ^ k n a
  have hQ (n : Fin T) : Q n ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun a _ => pow_ne_zero _ (hnonzero a)
  have hsum (n : Fin T) :
      (∑ i, (R n i).eval₂ (Polynomial.aeval θ).toRingHom ν * c i) =
        Q n * ∑ i : I, c i * iteratedDeriv n
          (clearedAdditionMonomial L v M i.1 i.2.1 i.2.2) z := by
    simp only [heval, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    change (Q n * _) * c i = Q n * (c i * _)
    ring
  constructor
  · intro hequations
    apply hcancel.mp
    intro n hn
    exact (mul_eq_zero.mp ((hsum ⟨n, hn⟩).symm.trans
      (hequations ⟨n, hn⟩))).resolve_left (hQ ⟨n, hn⟩)
  · intro hvanish n
    rw [hsum, hcancel.mpr hvanish n n.isLt, mul_zero]

end WeierstrassEllipticZeta

open WeierstrassEllipticZeta

-- Closed construction helpers extracted from Sol_WeierstrassEllipticZeta_exists_complex_auxiliary_systems_from_cleared_entire_data.lean
noncomputable section
set_option maxHeartbeats 800000
open MvPolynomial
open scoped Polynomial
namespace WeierstrassEllipticZeta

private def p2mL8_5_flatten : ℤ[X][X] →+* MvPolynomial (Fin 2) ℤ :=
  Polynomial.eval₂RingHom (Polynomial.eval₂RingHom C (X 0)) (X 1)

private lemma p2mL8_5_flatten_eval (p : ℤ[X][X]) (θ ν : ℂ) :
    eval₂ (Int.castRingHom ℂ) ![θ, ν] (p2mL8_5_flatten p) =
      p.eval₂ (Polynomial.aeval θ).toRingHom ν := by
  have h : (eval₂Hom (Int.castRingHom ℂ) ![θ, ν]).comp p2mL8_5_flatten =
      Polynomial.eval₂RingHom (Polynomial.aeval θ).toRingHom ν := by
    apply Polynomial.ringHom_ext
    · intro q
      have hq : (eval₂Hom (Int.castRingHom ℂ) ![θ, ν]).comp
          (Polynomial.eval₂RingHom C (X 0)) = (Polynomial.aeval θ).toRingHom := by
        apply Polynomial.ringHom_ext <;> simp
      simpa [p2mL8_5_flatten] using congrArg (fun f : ℤ[X] →+* ℂ => f q) hq
    · simp [p2mL8_5_flatten]
  exact congrArg (fun f : ℤ[X][X] →+* ℂ => f p) h

private theorem p2mL8_5_period_arithmetic_jet_systems (L : PeriodPair) (ω z θ ν : ℂ)
    (hzeta : ∀ w : ℂ, w ∉ L.lattice →
      HasDerivAt (weierstrassZeta L) (-L.weierstrassP w) w)
    (hperiod : ∀ (w : ℂ) (a : ℤ), w ∉ L.lattice →
      L.weierstrassP (w + a * ω) = L.weierstrassP w ∧
      weierstrassZeta L (w + a * ω) = weierstrassZeta L w + a * zetaQuasiPeriod L ω)
    (hregular : ∀ a : ℤ, z + a * ω ∉ L.lattice)
    (g : ℤ[X][X]) (hg : g.Monic) (hg_degree : 0 < g.natDegree)
    (hg_zero : g.eval₂ (Polynomial.aeval θ).toRingHom ν = 0)
    (d : ℤ[X]) (hd : Polynomial.aeval θ d ≠ 0)
    (hdata : ∀ i : Fin 7, ∃ p : ℤ[X][X],
      p.eval₂ (Polynomial.aeval θ).toRingHom ν =
        Polynomial.aeval θ d * periodJetCoordinates L ω z i) :
    PeriodArithmeticJetSystemData L ω z θ ν g d := by
  classical
  choose p hp using hdata
  let s : Fin 7 → MvPolynomial (Fin 2) ℤ := fun i => p2mL8_5_flatten (p i)
  let q : MvPolynomial (Fin 2) ℤ := p2mL8_5_flatten (Polynomial.C d)
  let D := 1 + q.totalDegree + Finset.univ.sup fun i => (s i).totalDegree
  let h := 1 + (∑ m ∈ q.support, (q.coeff m).natAbs) +
    Finset.univ.sup fun i => ∑ m ∈ (s i).support, ((s i).coeff m).natAbs
  let Bg := g.support.sup fun j => (g.coeff j).natDegree
  let Hg := 1 + ∑ j ∈ g.support, ∑ k ∈ (g.coeff j).support,
    ((g.coeff j).coeff k).natAbs
  have hDpos : 0 < D := by dsimp [D]; omega
  have hhpos : 0 < h := by dsimp [h]; omega
  have hHg : 1 ≤ Hg := by dsimp [Hg]; omega
  have hsD (i : Fin 7) : (s i).totalDegree ≤ D := by
    have := Finset.le_sup (f := fun i => (s i).totalDegree) (Finset.mem_univ i)
    dsimp [D]; omega
  have hqD : q.totalDegree ≤ D := by dsimp [D]; omega
  have hsh (i : Fin 7) : (∑ m ∈ (s i).support, ((s i).coeff m).natAbs) ≤ h := by
    have := Finset.le_sup (f := fun i => ∑ m ∈ (s i).support,
      ((s i).coeff m).natAbs) (Finset.mem_univ i)
    dsimp [h]; omega
  have hqh : (∑ m ∈ q.support, (q.coeff m).natAbs) ≤ h := by dsimp [h]; omega
  have hBg (i : ℕ) : (g.coeff i).natDegree ≤ Bg := by
    by_cases hi : i ∈ g.support
    · exact Finset.le_sup (f := fun i => (g.coeff i).natDegree) hi
    · simp [Polynomial.notMem_support_iff.mp hi]
  let B := (Bg + 1) * (7 * D)
  let H := h ^ 7 * Hg ^ (7 * D + 1)
  refine ⟨B, H, by dsimp [B]; positivity, by dsimp [H]; positivity, ?_⟩
  intro a M L₀ T
  dsimp only
  let I := Fin (L₀ + 1) × Fin (M + 1) × Fin (M + 1)
  let K : ℕ → ℕ := fun n => L₀ + 2 * M + n
  have hall (n : Fin T) (i : I) : ∃ r : ℤ[X][X],
      r.natDegree < g.natDegree ∧ (∀ j, (r.coeff j).natDegree ≤ B * K n) ∧
      (∑ j ∈ r.support, ∑ k ∈ (r.coeff j).support, ((r.coeff j).coeff k).natAbs) ≤
        n.val.factorial * 24 ^ K n * (1 + a.natAbs) ^ (L₀ + M) * H ^ (K n + 1) ∧
      r.eval₂ (Polynomial.aeval θ).toRingHom ν = Polynomial.aeval θ d ^ (7 * K n) *
        iteratedDeriv n (fun w => w ^ i.1.val * L.weierstrassP w ^ i.2.1.val *
          weierstrassZeta L w ^ i.2.2.val) (z + a * ω) := by
    let P := periodJetDerivation^[n.val] (periodJetPolynomial a i.1 i.2.1 i.2.2)
    have hj := period_translate_polynomial_jets L ω hzeta hperiod a i.1 i.2.1 i.2.2 n
    have hsum : i.1.val + i.2.1.val + i.2.2.val + n.val ≤ K n := by
      have := i.1.isLt; have := i.2.1.isLt; have := i.2.2.isLt
      dsimp [K]; omega
    have hsum' : i.1.val + i.2.2.val ≤ L₀ + M := by
      have := i.1.isLt; have := i.2.2.isLt; omega
    have hP : P.totalDegree ≤ K n := hj.1.trans hsum
    obtain ⟨r, hrD, hrh, hreval⟩ := TranscendenceTheory.polynomial_clear_denominators_bound
      (A := ℂ) P (fun _ => K n) (fun _ => D) (fun _ => h) s (fun _ => q)
      (fun j => (degreeOf_le_totalDegree P j).trans hP) hsD (fun _ => hqD) hsh (fun _ => hqh)
    have hrD' : r.totalDegree ≤ 7 * D * K n := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using hrD
    have hrh' : (∑ m ∈ r.support, (r.coeff m).natAbs) ≤
        (n.val.factorial * 24 ^ K n * (1 + a.natAbs) ^ (L₀ + M)) * h ^ (7 * K n) := by
      apply hrh.trans
      have hbase := hj.2.1
      have hb := Nat.mul_le_mul
        (Nat.mul_le_mul_left n.val.factorial
          (Nat.pow_le_pow_right (by norm_num : 1 ≤ (24 : ℕ)) hsum))
        (Nat.pow_le_pow_right (by omega : 1 ≤ 1 + a.natAbs) hsum')
      simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul,
        Nat.mul_comm (K n) 7] using Nat.mul_le_mul_right (h ^ (K n * 7)) (hbase.trans hb)
    obtain ⟨r', hy, hx, hlen, heval⟩ :=
      TranscendenceTheory.bivariate_monic_reduction_bound g hg hg_degree Bg hBg r
    refine ⟨r', hy, ?_, ?_, ?_⟩
    · intro j
      simpa [B, mul_assoc] using (hx j).trans (Nat.mul_le_mul_left (Bg + 1) hrD')
    · apply hlen.trans
      change _ ≤ _ * H ^ (K n + 1)
      have he : r.totalDegree + 1 ≤ (7 * D + 1) * (K n + 1) := by nlinarith [hrD']
      calc
        _ ≤ ((n.val.factorial * 24 ^ K n * (1 + a.natAbs) ^ (L₀ + M)) *
            h ^ (7 * K n)) * Hg ^ ((7 * D + 1) * (K n + 1)) :=
          Nat.mul_le_mul hrh' (Nat.pow_le_pow_right hHg he)
        _ ≤ ((n.val.factorial * 24 ^ K n * (1 + a.natAbs) ^ (L₀ + M)) *
            h ^ (7 * (K n + 1))) * Hg ^ ((7 * D + 1) * (K n + 1)) :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _
            (Nat.pow_le_pow_right (by omega) (by omega)))
        _ = _ := by simp [H, mul_pow, ← pow_mul, mul_assoc]
    · have he := heval ℂ (Polynomial.aeval θ).toRingHom ν hg_zero
      simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, Polynomial.aeval_X] at he
      apply he.trans
      have hqeval : eval₂ (Int.castRingHom ℂ) ![θ, ν] q = Polynomial.aeval θ d := by
        simpa [q] using p2mL8_5_flatten_eval (Polynomial.C d) θ ν
      have hseval (j : Fin 7) : (eval₂Hom (Int.castRingHom ℂ) ![θ, ν]) (s j) =
          (eval₂Hom (Int.castRingHom ℂ) ![θ, ν]) q * periodJetCoordinates L ω z j := by
        change eval₂ _ _ (p2mL8_5_flatten (p j)) = _
        rw [p2mL8_5_flatten_eval, hp, show (eval₂Hom (Int.castRingHom ℂ) ![θ, ν]) q = _ from hqeval]
      have hv := hreval (eval₂Hom (Int.castRingHom ℂ) ![θ, ν])
        (periodJetCoordinates L ω z) hseval
      have hz : z ∉ L.lattice := by simpa using hregular 0
      change eval₂ (Int.castRingHom ℂ) ![θ, ν] r =
        (∏ _ : Fin 7, eval₂ (Int.castRingHom ℂ) ![θ, ν] q ^ K n) *
          eval₂ (Int.castRingHom ℂ) (periodJetCoordinates L ω z) P at hv
      dsimp only [P] at hv
      simpa only [hqeval, Finset.prod_const, Finset.card_univ,
        Fintype.card_fin, ← pow_mul, Nat.mul_comm, ← hj.2.2 z hz] using hv
  choose R hRy hRx hRH hReval using hall
  refine ⟨R, fun n i => ⟨hRy n i, hRx n i, hRH n i⟩, hReval, ?_⟩
  intro c
  have hZ : AnalyticAt ℂ (weierstrassZeta L) (z + a * ω) :=
    (show DifferentiableOn ℂ (weierstrassZeta L) L.latticeᶜ from
      fun w hw => (hzeta w hw).differentiableAt.differentiableWithinAt).analyticOnNhd
      L.isClosed_lattice.isOpen_compl _ (hregular a)
  have hmono (i : I) : AnalyticAt ℂ (fun w =>
      w ^ i.1.val * L.weierstrassP w ^ i.2.1.val * weierstrassZeta L w ^ i.2.2.val)
        (z + a * ω) :=
    ((analyticAt_id.pow _).mul ((L.analyticOnNhd_weierstrassP _ (hregular a)).pow _)).mul
      (hZ.pow _)
  have hsum (n : Fin T) : (∑ i, (R n i).eval₂ (Polynomial.aeval θ).toRingHom ν * c i) =
      Polynomial.aeval θ d ^ (7 * K n) * iteratedDeriv n (fun w =>
        ∑ i, c i * w ^ i.1.val * L.weierstrassP w ^ i.2.1.val *
          weierstrassZeta L w ^ i.2.2.val) (z + a * ω) := by
    simp_rw [mul_assoc (c _)]
    rw [iteratedDeriv_fun_sum (f := fun i w => c i *
      (w ^ i.1.val * L.weierstrassP w ^ i.2.1.val * weierstrassZeta L w ^ i.2.2.val))
        (fun i _ => (analyticAt_const.mul (hmono i)).contDiffAt)]
    simp only [iteratedDeriv_const_mul_field, Finset.mul_sum, hReval]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [mul_assoc]
    ring
  constructor
  · intro he n hn
    exact (mul_eq_zero.mp ((hsum ⟨n, hn⟩).symm.trans (he ⟨n, hn⟩))).resolve_left
      (pow_ne_zero _ hd)
  · intro he n
    rw [hsum, he n n.isLt, mul_zero]

end WeierstrassEllipticZeta

open WeierstrassEllipticZeta

-- Closed construction helpers extracted from Sol_WeierstrassEllipticZeta_exists_complex_auxiliary_systems_from_period_jet_systems.lean
open Filter

namespace WeierstrassEllipticZeta

private theorem p2mL8_6_auxiliary_grid_parameter_data (L : PeriodPair) (ω u₁ u₂ : ℂ)
    (h_grid : RegularAuxiliaryGridData L ω u₁ u₂) :
    AuxiliaryGridParameterData L ω u₁ u₂ := by
  intro B hB
  let U := ‖u₁‖ + ‖u₂‖ + ‖ω‖ + 1
  have hU : 0 < U := by dsimp [U]; positivity
  have hA : 0 < B + U := add_pos hB hU
  filter_upwards [auxiliary_parameter_estimates (B + U) hA] with N hN
  rcases hN with ⟨hm, hl, hs, hq, hsq, hgap, hlo, hhi, hlog, hls, hR, hrad, hgrowth⟩
  dsimp only
  have hcard : (shiftedAuxiliaryGrid u₁ u₂ ω
      ![auxiliaryS N, auxiliaryS N, auxiliaryS3 N]).card =
      auxiliaryS N ^ 2 * auxiliaryS3 N := by
    rw [h_grid.card_shifted_grid]
    simp [Fin.prod_univ_succ, pow_two, mul_assoc]
  rw [hcard]
  have hgap' : 8 * ((auxiliaryL0 N + 1) * (auxiliaryS N ^ 2 * auxiliaryS3 N)) ≤
      (auxiliaryL0 N + 1) * (auxiliaryL N + 1) ^ 2 := by simpa [mul_assoc] using hgap
  have hlo' : (N : ℝ) ^ 2 / 512 ≤
      (auxiliaryL0 N + 1 : ℝ) * ↑(auxiliaryS N ^ 2 * auxiliaryS3 N) := by
    simpa only [Nat.cast_mul, Nat.cast_pow, mul_assoc] using hlo
  have hhi' : (auxiliaryL0 N + 1 : ℝ) * ↑(auxiliaryS N ^ 2 * auxiliaryS3 N) ≤
      (N : ℝ) ^ 2 / 32 := by
    simpa only [Nat.cast_mul, Nat.cast_pow, mul_assoc] using hhi
  refine ⟨hm, hl, hs, hq, hsq, hgap', hlo', hhi', hlog, hls, hR, ?_, ?_, ?_, ?_⟩
  · change 0 < 4 * (auxiliaryS3 N : ℝ) * U
    have : 0 < (auxiliaryS3 N : ℝ) := by exact_mod_cast (by omega : 0 < auxiliaryS3 N)
    positivity
  · intro z hz
    refine ⟨h_grid.shifted_grid_regular _ z hz, ?_⟩
    have hzbound := h_grid.shifted_grid_radius _ z hz
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, Nat.cast_mul, Nat.cast_ofNat] at hzbound
    have hsq' : (auxiliaryS N : ℝ) ≤ auxiliaryS3 N := by exact_mod_cast hsq
    have hq' : (1 : ℝ) ≤ auxiliaryS3 N := by exact_mod_cast hq
    have hu1 := mul_le_mul_of_nonneg_right hsq' (norm_nonneg u₁)
    have hu2 := mul_le_mul_of_nonneg_right hsq' (norm_nonneg u₂)
    have hu3 := mul_le_mul_of_nonneg_right hq' (norm_nonneg u₁)
    nlinarith only [hzbound, hu1, hu2, hu3, hq',
      mul_nonneg (Nat.cast_nonneg (auxiliaryS3 N)) (norm_nonneg u₁),
      mul_nonneg (Nat.cast_nonneg (auxiliaryS3 N)) (norm_nonneg u₂),
      mul_nonneg (Nat.cast_nonneg (auxiliaryS3 N)) (norm_nonneg ω)]
  · change 2 * (4 * (auxiliaryS3 N : ℝ) * U) / auxiliaryRadius N ≤ _
    calc
      _ ≤ 8 * (B + U) * auxiliaryS3 N / auxiliaryRadius N := by
        apply div_le_div_of_nonneg_right _ (by linarith)
        nlinarith [mul_nonneg hB.le (Nat.cast_nonneg (auxiliaryS3 N))]
      _ ≤ _ := hrad
  · calc
      B * auxiliaryL N * auxiliaryRadius N ^ 2 ≤
          (B + U) * auxiliaryL N * auxiliaryRadius N ^ 2 := by
        apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
        apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
        linarith
      _ ≤ _ := hgrowth

end WeierstrassEllipticZeta

open WeierstrassEllipticZeta
open scoped Polynomial

open WeierstrassEllipticZeta
open scoped Polynomial
set_option maxHeartbeats 1600000

theorem solution
    (L : PeriodPair) (ω u₁ u₂ : ℂ)
    (h_grid : RegularAuxiliaryGridData L ω u₁ u₂)
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
    AuxiliaryGridJetMatrixData L ω u₁ u₂ θ ν g d := by
  have h_zeta_deriv := hasDerivAt_weierstrassZeta L
  have h_zeta_addition := zeta_addition_formula L
  have h_wp_addition := wp_addition_formula L
  have h_jets := p2mL8_0_cleared_addition_jet_data L h_zeta_deriv h_zeta_addition h_wp_addition
  have h_height := p2mL8_1_cleared_addition_height
  have h_arithmetic := p2mL8_2_arithmetic_jets_of_polynomial_jets L h_jets h_height
  have h_zero := (hg_kernel g).2 (dvd_refl g)
  have h_reduced := p2mL8_3_reduced_arithmetic_jets_of_arithmetic_jets
    L h_arithmetic θ ν g hg_monic hg_degree h_zero
  have h_systems := p2mL8_4_reduced_jet_systems_of_reduced_jets
    L h_zeta_deriv h_zeta_addition θ ν g h_reduced
  have hperiod (z : ℂ) (a : ℤ) (hz : z ∉ L.lattice) :=
    And.intro (h_grid.period_values z a hz).1 (h_grid.period_values z a hz).2.2
  have hregular (a : ℤ) : u₁ / 2 + a * ω ∉ L.lattice := by
    simpa [integerGridPoint, add_comm] using h_grid.shifted_regular ![0, 0, a]
  have hg_zero := (hg_kernel g).2 (dvd_refl g)
  have hdata : ∀ i : Fin 7, ∃ p : ℤ[X][X],
      p.eval₂ (Polynomial.aeval θ).toRingHom ν =
        Polynomial.aeval θ d * periodJetCoordinates L ω (u₁ / 2) i := by
    intro i
    fin_cases i
    · obtain ⟨p, _, hp⟩ := h_data 4
      exact ⟨p, by simpa [periodJetCoordinates] using hp⟩
    · obtain ⟨p, _, hp⟩ := h_data 2
      exact ⟨p, by simpa [periodJetCoordinates] using hp⟩
    · obtain ⟨p, _, hp⟩ := h_data 3
      exact ⟨p, by simpa [periodJetCoordinates] using hp⟩
    · obtain ⟨p, _, hp⟩ := h_data 6
      exact ⟨p, by simpa [periodJetCoordinates] using hp⟩
    · obtain ⟨p, _, hp⟩ := h_data 7
      exact ⟨p, by simpa [periodJetCoordinates] using hp⟩
    · obtain ⟨p, _, hp⟩ := h_data 8
      exact ⟨p, by simpa [periodJetCoordinates] using hp⟩
    · obtain ⟨p, _, hp⟩ := h_data 9
      exact ⟨p, by simpa [periodJetCoordinates] using hp⟩
  have h_period_jets := p2mL8_5_period_arithmetic_jet_systems L ω (u₁ / 2) θ ν
    h_zeta_deriv hperiod hregular g hg_monic hg_degree hg_zero d hd hdata
  have h_parameters := p2mL8_6_auxiliary_grid_parameter_data L ω u₁ u₂ h_grid
  have h_period_bounds := bounded_auxiliary_period_jet_systems
    L ω u₁ u₂ θ ν g d h_parameters h_period_jets
  have h_nonlattice_bounds := bounded_auxiliary_nonlattice_jet_systems
    L ω u₁ u₂ θ ν g h_parameters h_systems
  have h_coordinates := auxiliary_nonlattice_coordinate_presentations
    L ω u₁ u₂ h_grid h_zeta_deriv h_zeta_addition h_wp_addition θ ν g d hd h_data
  exact assemble_auxiliary_grid_jet_matrices L ω u₁ u₂ θ ν g d
    h_grid h_parameters h_coordinates h_nonlattice_bounds h_period_bounds
