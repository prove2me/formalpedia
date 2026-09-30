-- Prove2me | solution 1 for WeierstrassEllipticZeta.period_translate_polynomial_jets
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-07T14:35:01.937072+00:00
-- url     : https://prove2.me/submissions/63884790-56c5-4b5c-bd5f-c233485c5cee

import Definitions.Def_WeierstrassEllipticZeta_PeriodJets
import Theorems.Thm_TranscendenceTheory_polynomial_ode_iterated_deriv
import Theorems.Thm_TranscendenceTheory_polynomial_derivation_length_bound
import Theorems.Thm_WeierstrassEllipticZeta_hasDerivAt_derivWeierstrassP
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

noncomputable section
set_option maxHeartbeats 600000
open MvPolynomial Filter
open scoped Topology
open WeierstrassEllipticZeta

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

private lemma degree_neg (p : MvPolynomial (Fin 7) ℤ) :
    (-p).totalDegree = p.totalDegree := by simp [totalDegree]

private lemma jet_derivation_degree (i : Fin 7) :
    (periodJetDerivation (X i)).totalDegree ≤ 2 := by
  fin_cases i <;> simp [periodJetDerivation]
  have h₁ := totalDegree_mul (12 * X 4 : MvPolynomial (Fin 7) ℤ) (X 5)
  have h₂ := totalDegree_mul (C (12 : ℤ) : MvPolynomial (Fin 7) ℤ) (X 4)
  change (12 * X 4 : MvPolynomial (Fin 7) ℤ).totalDegree ≤ _ at h₂
  simp only [totalDegree_C, totalDegree_X] at h₁ h₂
  have hc : (12 : MvPolynomial (Fin 7) ℤ).totalDegree = 0 := totalDegree_C (12 : ℤ)
  omega

private lemma period_coordinates_ode (L : PeriodPair)
    (hzeta : ∀ z : ℂ, z ∉ L.lattice → HasDerivAt (weierstrassZeta L)
      (-L.weierstrassP z) z)
    (v z : ℂ) (hz : z ∉ L.lattice) (i : Fin 7) :
    HasDerivAt (fun w => periodJetCoordinates L v w i)
      (eval₂ (Int.castRingHom ℂ) (periodJetCoordinates L v z)
        (periodJetDerivation (X i))) z := by
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
  · simpa [periodJetCoordinates, periodJetDerivation] using hasDerivAt_id' z
  · simpa [periodJetCoordinates, periodJetDerivation] using hasDerivAt_const z v
  · simpa [periodJetCoordinates, periodJetDerivation] using
      hasDerivAt_const z (zetaQuasiPeriod L v)
  · simpa [periodJetCoordinates, periodJetDerivation] using hzeta z hz
  · simpa [periodJetCoordinates, periodJetDerivation] using hP
  · simpa [periodJetCoordinates, periodJetDerivation, hD.deriv] using hD
  · simpa [periodJetCoordinates, periodJetDerivation] using hDD

private lemma polyLength_C (a : ℤ) :
    polyLength (C a : MvPolynomial (Fin 7) ℤ) = a.natAbs :=
  polyLength_monomial 0 a

private lemma polyLength_X (i : Fin 7) :
    polyLength (X i : MvPolynomial (Fin 7) ℤ) = 1 :=
  polyLength_monomial _ 1

private lemma polyLength_neg (p : MvPolynomial (Fin 7) ℤ) :
    polyLength (-p) = polyLength p := by simp [polyLength]

private lemma length_mul_le {p q : MvPolynomial (Fin 7) ℤ} {a b : ℕ}
    (hp : polyLength p ≤ a) (hq : polyLength q ≤ b) :
    polyLength (p * q) ≤ a * b :=
  (polyLength_mul p q).trans (Nat.mul_le_mul hp hq)

private lemma length_pow_le {p : MvPolynomial (Fin 7) ℤ} {a : ℕ}
    (hp : polyLength p ≤ a) (n : ℕ) : polyLength (p ^ n) ≤ a ^ n :=
  (polyLength_pow p n).trans (Nat.pow_le_pow_left hp n)

private lemma jet_derivation_length (i : Fin 7) :
    polyLength (periodJetDerivation (X i)) ≤ 12 := by
  have h0 : polyLength (0 : MvPolynomial (Fin 7) ℤ) = 0 := by simpa using polyLength_C 0
  have h1 : polyLength (1 : MvPolynomial (Fin 7) ℤ) = 1 := polyLength_C 1
  fin_cases i <;> simp [periodJetDerivation, polyLength_X, polyLength_neg, h0, h1]
  simpa using length_mul_le
    (length_mul_le (polyLength_C 12).le (polyLength_X 4).le) (polyLength_X 5).le

private lemma period_polynomial_degree (a : ℤ) (l₀ l₂ l₃ : ℕ) :
    (periodJetPolynomial a l₀ l₂ l₃).totalDegree ≤ l₀ + l₂ + l₃ := by
  have hlin (i j : Fin 7) :
      (X i + C a * X j : MvPolynomial (Fin 7) ℤ).totalDegree ≤ 1 := by
    apply (totalDegree_add _ _).trans
    apply max_le (by simp)
    simpa only [totalDegree_C, totalDegree_X, zero_add] using
      totalDegree_mul (C a : MvPolynomial (Fin 7) ℤ) (X j)
  unfold periodJetPolynomial
  apply (totalDegree_mul _ _).trans
  apply (Nat.add_le_add (totalDegree_mul _ _) (totalDegree_pow _ _)).trans
  have h0 := (totalDegree_pow (X 0 + C a * X 1 : MvPolynomial (Fin 7) ℤ) l₀).trans
    (Nat.mul_le_mul_left l₀ (hlin 0 1))
  have h3 := Nat.mul_le_mul_left l₃ (hlin 3 2)
  simp only [totalDegree_X_pow, mul_one] at h0 h3 ⊢
  omega

private lemma period_polynomial_length (a : ℤ) (l₀ l₂ l₃ : ℕ) :
    polyLength (periodJetPolynomial a l₀ l₂ l₃) ≤ (1 + a.natAbs) ^ (l₀ + l₃) := by
  have hlin (i j : Fin 7) :
      polyLength (X i + C a * X j : MvPolynomial (Fin 7) ℤ) ≤ 1 + a.natAbs := by
    apply (polyLength_add _ _).trans
    simpa only [polyLength_X, mul_one] using Nat.add_le_add (polyLength_X i).le
      (length_mul_le (polyLength_C a).le (polyLength_X j).le)
  unfold periodJetPolynomial
  simpa [pow_add] using length_mul_le
    (length_mul_le (length_pow_le (hlin 0 1) l₀)
      (length_pow_le (polyLength_X 4).le l₂)) (length_pow_le (hlin 3 2) l₃)

theorem solution (L : PeriodPair) (ω : ℂ)
    (hzeta : ∀ z : ℂ, z ∉ L.lattice →
      HasDerivAt (weierstrassZeta L) (-L.weierstrassP z) z)
    (hperiod : ∀ (z : ℂ) (a : ℤ), z ∉ L.lattice →
      L.weierstrassP (z + a * ω) = L.weierstrassP z ∧
      weierstrassZeta L (z + a * ω) = weierstrassZeta L z + a * zetaQuasiPeriod L ω)
    (a : ℤ) (l₀ l₂ l₃ n : ℕ) :
    (periodJetDerivation^[n] (periodJetPolynomial a l₀ l₂ l₃)).totalDegree ≤
      l₀ + l₂ + l₃ + n ∧
    (∑ m ∈ (periodJetDerivation^[n] (periodJetPolynomial a l₀ l₂ l₃)).support,
      ((periodJetDerivation^[n] (periodJetPolynomial a l₀ l₂ l₃)).coeff m).natAbs) ≤
        n.factorial * 24 ^ (l₀ + l₂ + l₃ + n) * (1 + a.natAbs) ^ (l₀ + l₃) ∧
    ∀ z : ℂ, z ∉ L.lattice →
      iteratedDeriv n (fun w => w ^ l₀ * L.weierstrassP w ^ l₂ *
        weierstrassZeta L w ^ l₃) (z + a * ω) =
          eval₂ (Int.castRingHom ℂ) (periodJetCoordinates L ω z)
            (periodJetDerivation^[n] (periodJetPolynomial a l₀ l₂ l₃)) := by
  have hdeg := period_polynomial_degree a l₀ l₂ l₃
  have hlen := period_polynomial_length a l₀ l₂ l₃
  have hb := TranscendenceTheory.polynomial_derivation_length_bound
    periodJetDerivation jet_derivation_degree 12 (by omega) jet_derivation_length
    (periodJetPolynomial a l₀ l₂ l₃) n
  refine ⟨hb.1.trans (Nat.add_le_add_right hdeg n), ?_, ?_⟩
  · apply hb.2.trans
    calc
      _ ≤ (1 + a.natAbs) ^ (l₀ + l₃) * n.factorial *
          24 ^ (l₀ + l₂ + l₃ + n) :=
        Nat.mul_le_mul (Nat.mul_le_mul_right _ hlen)
          (Nat.pow_le_pow_right (by omega) (Nat.add_le_add_right hdeg n))
      _ = _ := by ring
  · intro z hz
    have hjet := (TranscendenceTheory.polynomial_ode_iterated_deriv
      periodJetDerivation jet_derivation_degree (L.lattice : Set ℂ)ᶜ
      L.isClosed_lattice.isOpen_compl (fun i w => periodJetCoordinates L ω w i)
      (fun w hw i => period_coordinates_ode L hzeta ω w hw i)
      (periodJetPolynomial a l₀ l₂ l₃) n).2 z hz
    have heq : (fun w => (w + a * ω) ^ l₀ * L.weierstrassP (w + a * ω) ^ l₂ *
        weierstrassZeta L (w + a * ω) ^ l₃) =ᶠ[𝓝 z]
        (fun w => eval₂ (Int.castRingHom ℂ) (periodJetCoordinates L ω w)
          (periodJetPolynomial a l₀ l₂ l₃)) := by
      filter_upwards [L.isClosed_lattice.isOpen_compl.mem_nhds hz] with w hw
      simp only [periodJetPolynomial, eval₂_mul, eval₂_pow, eval₂_add, eval₂_C, eval₂_X]
      simp [periodJetCoordinates, (hperiod w a hw).1,
        (hperiod w a hw).2]
    have hi := heq.iteratedDeriv_eq n
    have ht := congrFun (iteratedDeriv_comp_add_const (n := n)
      (f := fun w => w ^ l₀ * L.weierstrassP w ^ l₂ * weierstrassZeta L w ^ l₃)
      (s := (a : ℂ) * ω)) z
    exact ht.symm.trans (hi.trans hjet)

