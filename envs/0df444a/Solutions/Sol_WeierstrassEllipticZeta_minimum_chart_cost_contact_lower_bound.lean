-- Prove2me | solution 1 for WeierstrassEllipticZeta.minimum_chart_cost_contact_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-23T00:26:16.864205+00:00
-- url     : https://prove2.me/submissions/4efcfe74-a8fa-4f55-ac1a-05acc4ef406d

import Theorems.Thm_WeierstrassEllipticZeta_elliptic_chart_canonical_base
import Theorems.Thm_WeierstrassEllipticZeta_elliptic_chart_global_base
import Theorems.Thm_WeierstrassEllipticZeta_elliptic_first_chart_relation_ideal
import Theorems.Thm_WeierstrassEllipticZeta_elliptic_chart_cubic_relation_ideals
import Theorems.Thm_WeierstrassEllipticZeta_elliptic_chart_finite_jet_generators
import Theorems.Thm_WeierstrassEllipticZeta_elliptic_chart_analytic_orbit
import Theorems.Thm_WeierstrassEllipticZeta_canonical_capped_chart_cost
import Theorems.Thm_WeierstrassEllipticZeta_minimum_chart_cost_selection
import Theorems.Thm_TranscendenceTheory_three_step_minimal_prime_selection
import Theorems.Thm_TranscendenceTheory_differential_prolongation_component_persistence
import Theorems.Thm_TranscendenceTheory_analytic_orbit_transverse_derivative
import Theorems.Thm_TranscendenceTheory_differential_prime_localization
import Theorems.Thm_TranscendenceTheory_differential_contact_length_lower_bound
import Definitions.Def_WeierstrassEllipticZeta_ChartSelectionData
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.Tactic

noncomputable section
namespace WeierstrassEllipticZeta
open TranscendenceTheory
open scoped Pointwise
private theorem cost_select_component
    (L : PeriodPair) (S : Fin 5 → ℂ → ℂ) (Q : MvPolynomial (Fin 7) ℂ) (T e : ℕ)
    (w : ChartSelectionMultiplicityData L S Q T e) :
    Nonempty (ChartProlongationMultiplicityData L S Q T e) := by
  classical
  let δ := extensionChartDerivation L.g₂ L.g₃ w.chart
  let q := RingHom.ker (MvPolynomial.eval (extensionChartCoordinates S w.chart w.z))
  let : q.IsPrime := RingHom.ker_isPrime _
  let J : Fin 4 → Ideal (MvPolynomial (Fin 4) ℂ) :=
    fun i => differentialProlongation δ w.base (i.val * T)
  have hzero : differentialProlongation δ w.base 0 = w.base := by
    apply le_antisymm
    · apply Ideal.span_le.mpr
      rintro r ⟨f, hf, k, hk, heq⟩
      have : k = 0 := Nat.eq_zero_of_le_zero hk
      subst k
      simpa using heq ▸ hf
    · intro f hf
      exact Ideal.subset_span ⟨f, hf, 0, le_refl 0, rfl⟩
  have hmono : Monotone J := by
    intro i j hij
    apply Ideal.span_mono
    rintro r ⟨f, hf, k, hk, heq⟩
    exact ⟨f, hf, k, hk.trans (Nat.mul_le_mul_right T hij), heq⟩
  have hdim : ringKrullDim (MvPolynomial (Fin 4) ℂ) = 4 := by simp
  have hupper : q.height ≤ (4 : ℕ∞) := by
    have h := q.height_le_ringKrullDim_of_isPrime
    rw [hdim] at h
    exact WithBot.coe_le_coe.mp h
  have hlower : (2 : ℕ∞) ≤ (J 0).height := by
    simpa only [J, Fin.val_zero, zero_mul, hzero] using w.height_lower
  obtain ⟨i, p, hpq, hstart, hend⟩ := three_step_minimal_prime_selection
    (MvPolynomial (Fin 4) ℂ) J hmono q w.terminal hlower hupper
  have hstart' : p ∈ (differentialProlongation δ w.base (i.val * T)).minimalPrimes :=
    hstart
  have hend' : p ∈ (differentialProlongation δ w.base ((i.val + 1) * T)).minimalPrimes :=
    hend
  let : p.IsPrime := hstart'.isPrime
  refine ⟨{
    chart := w.chart
    z := w.z
    chart_ne := w.chart_ne
    base := w.base
    stage := i.val * T
    p := p
    minimal_start := hstart'
    minimal_end := ?_
    normalized_mem := hstart'.le (Ideal.subset_span
      ⟨_, w.normalized_mem, 0, Nat.zero_le _, rfl⟩)
    point_on_prime := ?_
    length_le := w.length_le i p hpq hstart' hend'
  }⟩
  · simpa only [Nat.add_mul, one_mul] using hend'
  · intro r hr
    exact RingHom.mem_ker.mp (hpq hr)


private theorem prolongation_budget_lower
    (L : PeriodPair) (D : EllipticSigmaDifferentialData L)
    (S : Fin 5 → ℂ → ℂ)
    (hS : ∀ j, AnalyticOnNhd ℂ (S j) Set.univ)
    (hS_value : ∀ z : ℂ, z ∉ L.lattice → ∀ j : Fin 5,
      S j z = D.sigma z ^ 3 * ![1, L.weierstrassP z, L.derivWeierstrassP z,
        weierstrassZeta L z,
        L.derivWeierstrassP z * weierstrassZeta L z + 2 * L.weierstrassP z ^ 2] j)
    (Q : MvPolynomial (Fin 7) ℂ) (n T e : ℕ)
    (hQ : ∀ d ∈ Q.support, d 2 + d 3 + d 4 + d 5 + d 6 = n)
    (hne : (fun z : ℂ => MvPolynomial.eval
      ![1, z, S 0 z, S 1 z, S 2 z, S 3 z, S 4 z] Q) ≠ 0)
    (w : ChartProlongationMultiplicityData L S Q T e) : T + 1 ≤ e := by
  let R := MvPolynomial (Fin 4) ℂ
  let δ := (extensionChartDerivation L.g₂ L.g₃ w.chart).restrictScalars ℚ
  let I := differentialProlongation (extensionChartDerivation L.g₂ L.g₃ w.chart)
    w.base w.stage
  have hjets : ∀ f ∈ I, ∀ k ≤ T, (δ^[k]) f ∈ w.p :=
    ((differential_prolongation_component_persistence ℂ R
      (extensionChartDerivation L.g₂ L.g₃ w.chart) w.base).2.2
        w.stage T w.p w.minimal_start).mp w.minimal_end
  obtain ⟨φ, hφ, hδ, ha, hf⟩ := elliptic_chart_analytic_orbit
    L D S hS hS_value Q n hQ hne w.chart w.z w.chart_ne
  obtain ⟨_, k, _, _, hmem, hnext⟩ := analytic_orbit_transverse_derivative
    R δ w.p φ w.z hδ (fun r hr => (hφ r w.z).trans (w.point_on_prime r hr))
    (extensionChartNormalize w.chart Q) w.normalized_mem ha hf
  let q := (δ^[k]) (extensionChartNormalize w.chart Q)
  have hescape : δ q ∉ w.p := by
    simpa only [q, Function.iterate_succ_apply'] using hnext
  obtain ⟨d, hd, hlocal⟩ := differential_prime_localization R δ w.p
  have hlow := differential_contact_length_lower_bound
    (Localization.AtPrime w.p) d (IsLocalRing.maximalIdeal (Localization.AtPrime w.p))
    (algebraMap R (Localization.AtPrime w.p) q)
    ((IsLocalization.AtPrime.to_map_mem_maximal_iff _ w.p _).mpr hmem)
    (by
      intro h
      rw [hd] at h
      exact hescape ((IsLocalization.AtPrime.to_map_mem_maximal_iff _ w.p _).mp h))
    (I.map (algebraMap R (Localization.AtPrime w.p))) T ((hlocal I T).mp hjets)
  exact_mod_cast hlow.trans w.length_le


end WeierstrassEllipticZeta
open WeierstrassEllipticZeta TranscendenceTheory
open scoped Pointwise

theorem solution
    (L : PeriodPair) (D : EllipticSigmaDifferentialData L)
    (S : Fin 5 → ℂ → ℂ)
    (hS : ∀ j, AnalyticOnNhd ℂ (S j) Set.univ)
    (hS_value : ∀ z : ℂ, z ∉ L.lattice → ∀ j : Fin 5,
      S j z = D.sigma z ^ 3 * ![1, L.weierstrassP z, L.derivWeierstrassP z,
        weierstrassZeta L z,
        L.derivWeierstrassP z * weierstrassZeta L z + 2 * L.weierstrassP z ^ 2] j)
    (hS_ne : ∀ z : ℂ, ∃ j : Fin 5, S j z ≠ 0)
    (Q : MvPolynomial (Fin 7) ℂ) (n N T : ℕ) (X : Finset ℂ)
    (h0 : 0 ∈ X)
    (hQ : ∀ d ∈ Q.support, d 2 + d 3 + d 4 + d 5 + d 6 = n)
    (hne : (fun z : ℂ => MvPolynomial.eval
      ![1, z, S 0 z, S 1 z, S 2 z, S 3 z, S 4 z] Q) ≠ 0)
    (hcap : ∀ (c : Fin 2) (t : ℕ), extensionChartJetIdeal L Q c t =
      extensionChartJetIdeal L Q c (min t N))
    (hhigh : ∀ z ∈ X + X + X, ∀ c : Fin 2,
      S (extensionChartDenominator c) z ≠ 0 →
      ((3 * T + 1 : ℕ) : ℕ∞) ≤ analyticOrderAt
        (fun w : ℂ => MvPolynomial.eval
          ![1, w, S 0 w / S (extensionChartDenominator c) w,
            S 1 w / S (extensionChartDenominator c) w,
            S 2 w / S (extensionChartDenominator c) w,
            S 3 w / S (extensionChartDenominator c) w,
            S 4 w / S (extensionChartDenominator c) w] Q) z) :
    (∀ e : ℕ, CappedChartJetBudget L S Q N T e (X + X + X) → T + 1 ≤ e) ∧
    (∀ (c : Fin 2) (z : ℂ), z ∈ X + X + X →
      S (extensionChartDenominator c) z ≠ 0 →
      T + 1 ≤ cappedChartCost L S Q N T c z) ∧
    T + 1 ≤ minimumChartCost L S Q N T X := by
  have hbudget (e : ℕ) (w : CappedChartJetBudget L S Q N T e (X + X + X)) :
      T + 1 ≤ e := by
    have hbase := elliptic_chart_canonical_base L D S hS hS_value Q n hQ hne
      w.chart w.z w.chart_ne (3 * T) (hhigh w.z w.z_mem w.chart w.chart_ne)
    have heqbase : extensionChartBaseIdeal S Q w.chart w.z =
        extensionCubicChartBaseIdeal L Q w.chart := by
      rw [((elliptic_chart_global_base S hS).1 w.chart w.z w.chart_ne).2 Q,
        ← (elliptic_first_chart_relation_ideal L D S hS hS_value hS_ne).2 Q w.chart,
        ← (elliptic_chart_cubic_relation_ideals L D S hS hS_value hS_ne).2 Q w.chart]
    have heq (t : ℕ) : differentialProlongation
        (extensionChartDerivation L.g₂ L.g₃ w.chart)
        (extensionChartBaseIdeal S Q w.chart w.z) t =
        extensionChartJetIdeal L Q w.chart (min t N) := by
      rw [heqbase, (elliptic_chart_finite_jet_generators L Q w.chart t).1, hcap]
    obtain ⟨v⟩ := cost_select_component L S Q T e {
      chart := w.chart
      z := w.z
      chart_ne := w.chart_ne
      base := extensionChartBaseIdeal S Q w.chart w.z
      height_lower := hbase.1
      normalized_mem := hbase.2.1
      terminal := hbase.2.2
      length_le := by
        intro i p hp hpq hs ht
        rw [heq] at hs ht ⊢
        exact w.length_le i p hpq hs ht
    }
    exact prolongation_budget_lower L D S hS hS_value Q n T e hQ hne v
  have hcost (c : Fin 2) (z : ℂ) (hz : z ∈ X + X + X)
      (hc : S (extensionChartDenominator c) z ≠ 0) :
      T + 1 ≤ cappedChartCost L S Q N T c z := by
    obtain ⟨w, _, _⟩ := ((canonical_capped_chart_cost L S Q N T (X + X + X)).1
      c z).2.2 hz hc
    exact hbudget _ w
  refine ⟨hbudget, hcost, ?_⟩
  obtain ⟨c, z, hz, hc, he⟩ :=
    ((minimum_chart_cost_selection L D S hS hS_value).2 Q N T X h0).2.2.2.2.1
  rw [← he]
  exact hcost c z hz hc
