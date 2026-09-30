-- Prove2me | solution 4 for WeierstrassEllipticZeta.senthil_kumar_theorem_one
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-23T04:24:20.754457+00:00
-- url     : https://prove2.me/submissions/b9796a6c-8341-47d3-af02-9a915b6195b8

import Definitions.Def_TranscendenceTheory_ComplexAuxiliarySystem
import Definitions.Def_WeierstrassEllipticZeta_ArithmeticJets
import Definitions.Def_WeierstrassEllipticZeta_AuxiliaryGrids
import Definitions.Def_WeierstrassEllipticZeta_AuxiliaryParameters
import Definitions.Def_WeierstrassEllipticZeta_ClearedEntire
import Definitions.Def_WeierstrassEllipticZeta_DifferentialPolynomials
import Definitions.Def_WeierstrassEllipticZeta_EntireRegularization
import Definitions.Def_WeierstrassEllipticZeta_GridInterpolation
import Definitions.Def_WeierstrassEllipticZeta_GridJetMatrices
import Definitions.Def_WeierstrassEllipticZeta_InterpolationDecay
import Definitions.Def_WeierstrassEllipticZeta_NonlatticeJetBounds
import Definitions.Def_WeierstrassEllipticZeta_PeriodJetBounds
import Definitions.Def_WeierstrassEllipticZeta_PeriodJets
import Definitions.Def_WeierstrassEllipticZeta_ReducedArithmeticJets
import Definitions.Def_WeierstrassEllipticZeta_ReducedJetSystems
import Definitions.Def_WeierstrassEllipticZeta_SigmaDifferential
import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Set.Card
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.RingTheory.Algebraic.Defs
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Topology.Separation.Hausdorff
import Theorems.Thm_TranscendenceTheory_bihomogeneous_lift_four_variables
import Theorems.Thm_TranscendenceTheory_bivariate_monic_reduction_bound
import Theorems.Thm_TranscendenceTheory_bounded_system_of_complex_auxiliary_system
import Theorems.Thm_TranscendenceTheory_exists_entire_monomial_regularization
import Theorems.Thm_TranscendenceTheory_exists_integral_generator_and_common_denominator
import Theorems.Thm_TranscendenceTheory_exists_reduced_bivariate_model
import Theorems.Thm_TranscendenceTheory_finite_set_subgroup_obstruction_exclusion
import Theorems.Thm_TranscendenceTheory_finite_zeros_derivative_bound
import Theorems.Thm_TranscendenceTheory_finite_zeros_exponential_derivative_bound
import Theorems.Thm_TranscendenceTheory_gelfond_polynomial_sequence_lower_bound
import Theorems.Thm_TranscendenceTheory_integer_grid_geometry
import Theorems.Thm_TranscendenceTheory_polynomial_clear_denominators_bound
import Theorems.Thm_TranscendenceTheory_polynomial_derivation_length_bound
import Theorems.Thm_TranscendenceTheory_polynomial_ode_iterated_deriv
import Theorems.Thm_TranscendenceTheory_projective_chart_vanishing_order
import Theorems.Thm_TranscendenceTheory_small_integral_coordinates_of_bivariate_values
import Theorems.Thm_TranscendenceTheory_small_polynomials_of_small_integral_elements
import Theorems.Thm_TranscendenceTheory_small_values_of_bounded_bivariate_systems
import Theorems.Thm_WeierstrassEllipticZeta_algebraic_auxiliary_values
import Theorems.Thm_WeierstrassEllipticZeta_assemble_auxiliary_grid_jet_matrices
import Theorems.Thm_WeierstrassEllipticZeta_auxiliary_function_nonvanishing
import Theorems.Thm_WeierstrassEllipticZeta_auxiliary_grid_quotient_geometry
import Theorems.Thm_WeierstrassEllipticZeta_auxiliary_nonlattice_coordinate_presentations
import Theorems.Thm_WeierstrassEllipticZeta_auxiliary_parameter_estimates
import Theorems.Thm_WeierstrassEllipticZeta_auxiliary_zero_estimate_parameter_bounds
import Theorems.Thm_WeierstrassEllipticZeta_bounded_auxiliary_nonlattice_jet_systems
import Theorems.Thm_WeierstrassEllipticZeta_bounded_auxiliary_period_jet_systems
import Theorems.Thm_WeierstrassEllipticZeta_cleared_addition_entire_growth
import Theorems.Thm_WeierstrassEllipticZeta_cleared_addition_entire_growth_weighted
import Theorems.Thm_WeierstrassEllipticZeta_cleared_addition_jet_vanishing_iff
import Theorems.Thm_WeierstrassEllipticZeta_cleared_auxiliary_first_derivative
import Theorems.Thm_WeierstrassEllipticZeta_cleared_auxiliary_polynomial_presentation
import Theorems.Thm_WeierstrassEllipticZeta_complex_auxiliary_systems_of_bounded_grid_derivatives
import Theorems.Thm_WeierstrassEllipticZeta_elliptic_auxiliary_first_derivative_decay
import Theorems.Thm_WeierstrassEllipticZeta_exists_elliptic_sigma_differential_data
import Theorems.Thm_WeierstrassEllipticZeta_exists_elliptic_sigma_quadratic_growth
import Theorems.Thm_WeierstrassEllipticZeta_exists_transcendental_parameter_of_no_pair
import Theorems.Thm_WeierstrassEllipticZeta_finite_set_projective_multiplicity_obstruction
import Theorems.Thm_WeierstrassEllipticZeta_hasDerivAt_derivWeierstrassP
import Theorems.Thm_WeierstrassEllipticZeta_hasDerivAt_weierstrassZeta
import Theorems.Thm_WeierstrassEllipticZeta_nonlattice_common_denominator_bounds
import Theorems.Thm_WeierstrassEllipticZeta_period_translate_polynomial_jets
import Theorems.Thm_WeierstrassEllipticZeta_regularization_preserves_nonvanishing
import Theorems.Thm_WeierstrassEllipticZeta_regularized_nonzero_derivative_transfer
import Theorems.Thm_WeierstrassEllipticZeta_sigma_addition_from_differential
import Theorems.Thm_WeierstrassEllipticZeta_sigma_period_inverse_bounds
import Theorems.Thm_WeierstrassEllipticZeta_sigma_projective_coordinates_entire
import Theorems.Thm_WeierstrassEllipticZeta_sigma_regularized_coordinates_entire
import Theorems.Thm_WeierstrassEllipticZeta_weierstrassZeta_add_period
import Theorems.Thm_WeierstrassEllipticZeta_wp_addition_formula
import Theorems.Thm_WeierstrassEllipticZeta_zeta_addition_formula

/- Main theorem conditional on the existing multiplicity contract.
The shorter downstream construction removes redundant intermediate hypotheses. -/

-- Assembly: WeierstrassEllipticZeta.finite_set_projective_chart_zero_estimate
namespace MultiplicityCompactStep0
open _root_.WeierstrassEllipticZeta _root_.TranscendenceTheory

open WeierstrassEllipticZeta
open scoped Pointwise

theorem _root_.WeierstrassEllipticZeta.finite_set_projective_chart_zero_estimate
    (L : PeriodPair) (D : EllipticSigmaDifferentialData L)
    (S : Fin 5 → ℂ → ℂ)
    (hS : ∀ j, AnalyticOnNhd ℂ (S j) Set.univ)
    (hS_value : ∀ z : ℂ, z ∉ L.lattice → ∀ j : Fin 5,
      S j z = D.sigma z ^ 3 * ![1, L.weierstrassP z, L.derivWeierstrassP z,
        weierstrassZeta L z,
        L.derivWeierstrassP z * weierstrassZeta L z + 2 * L.weierstrassP z ^ 2] j)
    (hS_ne : ∀ z : ℂ, ∃ j : Fin 5, S j z ≠ 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ m n T : ℕ,
      1 ≤ m → 1 ≤ n → 3 ≤ T → ∀ X : Finset ℂ,
      0 ∈ X →
      3 * C * (m : ℝ) * (n : ℝ) ^ 2 < (T : ℝ) * X.card →
      3 * C * (n : ℝ) ^ 2 <
        (T : ℝ) * (L.lattice.mkQ '' (X : Set ℂ)).ncard →
      ∀ Q : MvPolynomial (Fin 7) ℂ,
        (∀ d ∈ Q.support, d 0 + d 1 = m ∧
          d 2 + d 3 + d 4 + d 5 + d 6 = n) →
        (fun z : ℂ => MvPolynomial.eval
          ![1, z, S 0 z, S 1 z, S 2 z, S 3 z, S 4 z] Q) ≠ 0 →
        ∃ v ∈ X + X + X, ∃ j : Fin 5, S j v ≠ 0 ∧
          analyticOrderAt
            (fun z : ℂ => MvPolynomial.eval
              ![1, z, S 0 z / S j z, S 1 z / S j z,
                S 2 z / S j z, S 3 z / S j z, S 4 z / S j z] Q) v ≤ T := by
  classical
  obtain ⟨C, hC, hobstruction⟩ :=
    finite_set_projective_multiplicity_obstruction L D S hS hS_value hS_ne
  refine ⟨C, hC, ?_⟩
  intro m n T hm hn hT X h0 hfirst hsecond Q hQ hF
  by_contra hno
  have hU : 1 ≤ T / 3 := by omega
  have hbound : 3 * (T / 3) + 1 ≤ T + 1 := by omega
  have hhigh : ∀ v ∈ X + X + X, ∀ j : Fin 5, S j v ≠ 0 →
      ((3 * (T / 3) + 1 : ℕ) : ℕ∞) ≤ analyticOrderAt
        (fun z : ℂ => MvPolynomial.eval
          ![1, z, S 0 z / S j z, S 1 z / S j z,
            S 2 z / S j z, S 3 z / S j z, S 4 z / S j z] Q) v := by
    intro v hv j hj
    have hnot : ¬ analyticOrderAt
        (fun z : ℂ => MvPolynomial.eval
          ![1, z, S 0 z / S j z, S 1 z / S j z,
            S 2 z / S j z, S 3 z / S j z, S 4 z / S j z] Q) v ≤ T :=
      fun hle => hno ⟨v, hv, j, hj, hle⟩
    have hsucc := (ENat.add_one_le_iff (by simp)).mpr (lt_of_not_ge hnot)
    have hbound' : ((3 * (T / 3) + 1 : ℕ) : ℕ∞) ≤ (T : ℕ∞) + 1 := by
      exact_mod_cast hbound
    exact hbound'.trans hsucc
  obtain ⟨K, a, b, hprofile, hb, hupper⟩ :=
    hobstruction m n (T / 3) hm hn hU X h0 Q hQ hF hhigh
  have hlower := TranscendenceTheory.finite_set_subgroup_obstruction_exclusion
    ℤ ℂ L.lattice X C hC m n T hm hn hfirst hsecond K a b hprofile hb
  exact (not_lt_of_ge hupper) hlower

end MultiplicityCompactStep0

-- Assembly: WeierstrassEllipticZeta.finite_set_projective_zero_estimate
namespace MultiplicityCompactStep1
open _root_.WeierstrassEllipticZeta _root_.TranscendenceTheory

open WeierstrassEllipticZeta
open scoped Pointwise

theorem _root_.WeierstrassEllipticZeta.finite_set_projective_zero_estimate
    (L : PeriodPair) (D : EllipticSigmaDifferentialData L)
    (S : Fin 5 → ℂ → ℂ)
    (hS : ∀ j, AnalyticOnNhd ℂ (S j) Set.univ)
    (hS_value : ∀ z : ℂ, z ∉ L.lattice → ∀ j : Fin 5,
      S j z = D.sigma z ^ 3 * ![1, L.weierstrassP z, L.derivWeierstrassP z,
        weierstrassZeta L z,
        L.derivWeierstrassP z * weierstrassZeta L z + 2 * L.weierstrassP z ^ 2] j)
    (hS_ne : ∀ z : ℂ, ∃ j : Fin 5, S j z ≠ 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ m n T : ℕ,
      1 ≤ m → 1 ≤ n → 3 ≤ T → ∀ X : Finset ℂ,
      0 ∈ X →
      3 * C * (m : ℝ) * (n : ℝ) ^ 2 < (T : ℝ) * X.card →
      3 * C * (n : ℝ) ^ 2 <
        (T : ℝ) * (L.lattice.mkQ '' (X : Set ℂ)).ncard →
      ∀ Q : MvPolynomial (Fin 7) ℂ,
        (∀ d ∈ Q.support, d 0 + d 1 = m ∧
          d 2 + d 3 + d 4 + d 5 + d 6 = n) →
        (fun z : ℂ => MvPolynomial.eval
          ![1, z, S 0 z, S 1 z, S 2 z, S 3 z, S 4 z] Q) ≠ 0 →
        ∃ v ∈ X + X + X, ∃ j : ℕ, j ≤ T ∧ iteratedDeriv j
          (fun z : ℂ => MvPolynomial.eval
            ![1, z, S 0 z, S 1 z, S 2 z, S 3 z, S 4 z] Q) v ≠ 0 := by
  obtain ⟨C, hC, hzero⟩ := finite_set_projective_chart_zero_estimate L D S hS hS_value hS_ne
  refine ⟨C, hC, ?_⟩
  intro m n T hm hn hT X h0 hfirst hsecond Q hQ hH
  obtain ⟨v, hv, j, hj, horder⟩ :=
    hzero m n T hm hn hT X h0 hfirst hsecond Q hQ hH
  have hlocal := TranscendenceTheory.projective_chart_vanishing_order
    ![fun _ : ℂ => 1, fun w : ℂ => w] S Q n (fun d hd => (hQ d hd).2) v j hj
    (by
      intro i
      fin_cases i
      · exact analyticAt_const
      · exact analyticAt_id)
    (fun i => hS i v trivial)
  obtain ⟨k, hk, hne⟩ := (hlocal.2.2.2 T).mp horder
  exact ⟨v, hv, k, hk, hne⟩

end MultiplicityCompactStep1

-- Assembly: WeierstrassEllipticZeta.projective_regularized_grid_zero_estimate
namespace MultiplicityCompactStep2
open _root_.WeierstrassEllipticZeta _root_.TranscendenceTheory

open WeierstrassEllipticZeta
open scoped Pointwise

theorem _root_.WeierstrassEllipticZeta.projective_regularized_grid_zero_estimate
    (L : PeriodPair) (ω u₁ u₂ : ℂ)
    (h_grid : RegularAuxiliaryGridData L ω u₁ u₂)
    (D : EllipticSigmaDifferentialData L)
    (S : Fin 5 → ℂ → ℂ)
    (hS : ∀ j, AnalyticOnNhd ℂ (S j) Set.univ)
    (hS_value : ∀ z : ℂ, z ∉ L.lattice → ∀ j : Fin 5,
      S j z = D.sigma z ^ 3 * ![1, L.weierstrassP z, L.derivWeierstrassP z,
        weierstrassZeta L z,
        L.derivWeierstrassP z * weierstrassZeta L z + 2 * L.weierstrassP z ^ 2] j)
    (hS_ne : ∀ z : ℂ, ∃ j : Fin 5, S j z ≠ 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ m l s q T : ℕ,
      1 ≤ m → 1 ≤ l → 1 ≤ s → 1 ≤ q → s ≤ q → l ≤ m → 3 ≤ T →
      3 * C * max ((m : ℝ) * (15 * l) ^ 2) ((q : ℝ) * (15 * l) ^ 2) <
        (T : ℝ) * (s : ℝ) ^ 2 * q →
      ∀ Q : MvPolynomial (Fin 7) ℂ,
        (∀ d ∈ Q.support, d 0 + d 1 = m ∧
          d 2 + d 3 + d 4 + d 5 + d 6 = 5 * l) →
        (fun z : ℂ => MvPolynomial.eval
          ![1, z, S 0 z, S 1 z, S 2 z, S 3 z, S 4 z] Q) ≠ 0 →
        ∃ v ∈ auxiliaryGrid u₁ u₂ ω ![3 * s, 3 * s, 3 * q],
          ∃ n : ℕ, n ≤ T ∧ iteratedDeriv n
            (fun z : ℂ => MvPolynomial.eval
              ![1, z, S 0 z, S 1 z, S 2 z, S 3 z, S 4 z] Q) v ≠ 0 := by
  obtain ⟨C, hC, hzero⟩ := finite_set_projective_zero_estimate L D S hS hS_value hS_ne
  refine ⟨C, hC, ?_⟩
  intro m l s q T hm hl hs hq hsq hlm hT hineq Q hQ hH
  have hA : ∀ i : Fin 3, 1 ≤ (![s, s, q] : Fin 3 → ℕ) i := by
    intro i
    fin_cases i <;> assumption
  obtain ⟨h0, htriple, hcard, hquot⟩ :=
    auxiliary_grid_quotient_geometry L ω u₁ u₂ h_grid ![s, s, q] hA
  have hpow : (5 * (l : ℝ)) ^ 2 ≤ (15 * (l : ℝ)) ^ 2 := by
    gcongr
    norm_num
  have hfirst : 3 * C * (m : ℝ) * ((5 * l : ℕ) : ℝ) ^ 2 <
      (T : ℝ) * (auxiliaryGrid u₁ u₂ ω ![s, s, q]).card := by
    rw [hcard]
    norm_num only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Nat.cast_mul, Nat.cast_ofNat]
    calc
      _ = 3 * C * ((m : ℝ) * (5 * (l : ℝ)) ^ 2) := by ring
      _ ≤ 3 * C * ((m : ℝ) * (15 * (l : ℝ)) ^ 2) := by gcongr
      _ ≤ 3 * C * max ((m : ℝ) * (15 * l) ^ 2) ((q : ℝ) * (15 * l) ^ 2) :=
        mul_le_mul_of_nonneg_left (le_max_left _ _) (by positivity)
      _ < (T : ℝ) * ((s : ℝ) * s * q) := by
        simpa [pow_two, mul_assoc] using hineq
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
  have hscaled : (3 * C * (5 * (l : ℝ)) ^ 2) * (q : ℝ) <
      ((T : ℝ) * (s : ℝ) ^ 2) * q := by
    calc
      _ = 3 * C * ((q : ℝ) * (5 * (l : ℝ)) ^ 2) := by ring
      _ ≤ 3 * C * ((q : ℝ) * (15 * (l : ℝ)) ^ 2) := by gcongr
      _ ≤ 3 * C * max ((m : ℝ) * (15 * l) ^ 2) ((q : ℝ) * (15 * l) ^ 2) :=
        mul_le_mul_of_nonneg_left (le_max_right _ _) (by positivity)
      _ < _ := hineq
  have hsecond : 3 * C * ((5 * l : ℕ) : ℝ) ^ 2 <
      (T : ℝ) * (L.lattice.mkQ '' (auxiliaryGrid u₁ u₂ ω ![s, s, q] : Set ℂ)).ncard := by
    rw [hquot]
    norm_num only [Matrix.cons_val_zero, Matrix.cons_val_one,
      Nat.cast_mul, Nat.cast_ofNat]
    simpa [pow_two] using (mul_lt_mul_iff_left₀ hqpos).mp hscaled
  obtain ⟨v, hv, j, hj, hne⟩ := hzero m (5 * l) T hm (by omega) hT
    (auxiliaryGrid u₁ u₂ ω ![s, s, q]) h0 hfirst hsecond Q hQ hH
  refine ⟨v, ?_, j, hj, hne⟩
  have hAeq : (fun i : Fin 3 => 3 * (![s, s, q] : Fin 3 → ℕ) i) =
      ![3 * s, 3 * s, 3 * q] := by
    funext i
    fin_cases i <;> rfl
  rw [hAeq] at htriple
  exact htriple hv

end MultiplicityCompactStep2

-- Assembly: WeierstrassEllipticZeta.bihomogeneous_regularized_grid_zero_estimate
namespace MultiplicityCompactStep3
open _root_.WeierstrassEllipticZeta _root_.TranscendenceTheory

open WeierstrassEllipticZeta

theorem _root_.WeierstrassEllipticZeta.bihomogeneous_regularized_grid_zero_estimate
    (L : PeriodPair) (ω u₁ u₂ : ℂ)
    (h_grid : RegularAuxiliaryGridData L ω u₁ u₂)
    (D : EllipticSigmaDifferentialData L) :
    ∃ C : ℝ, 0 < C ∧ ∀ m l s q T : ℕ,
      1 ≤ m → 1 ≤ l → 1 ≤ s → 1 ≤ q → s ≤ q → l ≤ m → 3 ≤ T →
      3 * C * max ((m : ℝ) * (15 * l) ^ 2) ((q : ℝ) * (15 * l) ^ 2) <
        (T : ℝ) * (s : ℝ) ^ 2 * q →
      ∀ (Q : MvPolynomial (Fin 7) ℂ) (G : ℂ → ℂ),
        (∀ d ∈ Q.support, d 0 + d 1 = m ∧
          d 2 + d 3 + d 4 + d 5 + d 6 = 5 * l) →
        AnalyticOnNhd ℂ G Set.univ →
        (∀ z : ℂ, z ∉ L.lattice →
          G z = MvPolynomial.eval ![1, z, D.sigma z ^ 3,
            D.sigma z ^ 3 * L.weierstrassP z,
            D.sigma z ^ 3 * L.derivWeierstrassP z,
            D.sigma z ^ 3 * weierstrassZeta L z,
            D.sigma z ^ 3 * (L.derivWeierstrassP z * weierstrassZeta L z +
              2 * L.weierstrassP z ^ 2)] Q) →
        G ≠ 0 → ∃ v ∈ auxiliaryGrid u₁ u₂ ω ![3 * s, 3 * s, 3 * q],
          ∃ n : ℕ, n ≤ T ∧ iteratedDeriv n G v ≠ 0 := by
  obtain ⟨S, hS, hS_value, hS_ne, _⟩ := sigma_projective_coordinates_entire L D
  obtain ⟨C, hC, hzero⟩ := projective_regularized_grid_zero_estimate L ω u₁ u₂ h_grid D
    S hS hS_value hS_ne
  refine ⟨C, hC, ?_⟩
  intro m l s q T hm hl hs hq hsq hlm hT hineq Q G hQ hG hG_value hG_ne
  let H : ℂ → ℂ := fun z => MvPolynomial.eval
    ![1, z, S 0 z, S 1 z, S 2 z, S 3 z, S 4 z] Q
  have hH : AnalyticOnNhd ℂ H Set.univ := by
    apply AnalyticOnNhd.aeval_mvPolynomial
    intro i z _
    fin_cases i
    · exact analyticAt_const
    · exact analyticAt_id
    · exact hS 0 z trivial
    · exact hS 1 z trivial
    · exact hS 2 z trivial
    · exact hS 3 z trivial
    · exact hS 4 z trivial
  have hHeq : G = H := by
    apply AnalyticOnNhd.eq_of_eventuallyEq hG hH (z₀ := L.ω₁ / 2)
    filter_upwards [L.isClosed_lattice.isOpen_compl.mem_nhds
      L.ω₁_div_two_notMem_lattice] with z hz
    rw [hG_value z hz]
    dsimp only [H]
    apply congrArg (fun t : Fin 7 → ℂ => MvPolynomial.eval t Q)
    funext i
    fin_cases i <;> simp [hS_value z hz]
  rw [hHeq]
  apply hzero m l s q T hm hl hs hq hsq hlm hT hineq Q hQ
  change H ≠ 0
  rwa [← hHeq]

end MultiplicityCompactStep3

-- Assembly: WeierstrassEllipticZeta.polynomial_regularized_grid_zero_estimate
namespace MultiplicityCompactStep4
open _root_.WeierstrassEllipticZeta _root_.TranscendenceTheory

open WeierstrassEllipticZeta

theorem _root_.WeierstrassEllipticZeta.polynomial_regularized_grid_zero_estimate
    (L : PeriodPair) (ω u₁ u₂ : ℂ)
    (h_grid : RegularAuxiliaryGridData L ω u₁ u₂)
    (D : EllipticSigmaDifferentialData L) :
    ∃ C : ℝ, 0 < C ∧ ∀ m l s q T : ℕ,
      1 ≤ m → 1 ≤ l → 1 ≤ s → 1 ≤ q → s ≤ q → l ≤ m → 3 ≤ T →
      3 * C * max ((m : ℝ) * (15 * l) ^ 2) ((q : ℝ) * (15 * l) ^ 2) <
        (T : ℝ) * (s : ℝ) ^ 2 * q →
      ∀ (P : MvPolynomial (Fin 4) ℂ) (G : ℂ → ℂ),
        (∀ d ∈ P.support, d 0 ≤ m ∧ d 1 + d 2 + d 3 ≤ 5 * l) →
        AnalyticOnNhd ℂ G Set.univ →
        (∀ z : ℂ, z ∉ L.lattice →
          G z = D.sigma z ^ (15 * l) *
            MvPolynomial.eval ![z, L.weierstrassP z, L.derivWeierstrassP z,
              weierstrassZeta L z] P) →
        G ≠ 0 → ∃ v ∈ auxiliaryGrid u₁ u₂ ω ![3 * s, 3 * s, 3 * q],
          ∃ n : ℕ, n ≤ T ∧ iteratedDeriv n G v ≠ 0 := by
  classical
  obtain ⟨C, hC, hzero⟩ := bihomogeneous_regularized_grid_zero_estimate L ω u₁ u₂ h_grid D
  refine ⟨C, hC, ?_⟩
  intro m l s q T hm hl hs hq hsq hlm hT hineq P G hP hG hG_value hG_ne
  obtain ⟨Q, hQ, hQ_value⟩ :=
    TranscendenceTheory.bihomogeneous_lift_four_variables ℂ P m (5 * l) hP
  apply hzero m l s q T hm hl hs hq hsq hlm hT hineq Q G
    (fun d hd => ⟨(hQ d hd).1, (hQ d hd).2.1⟩) hG ?_ hG_ne
  intro z hz
  rw [hG_value z hz]
  have hexp : (D.sigma z ^ 3) ^ (5 * l) = D.sigma z ^ (15 * l) := by
    rw [← pow_mul]
    congr 1
    omega
  rw [← hexp]
  symm
  simpa only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, one_mul, one_pow] using
    hQ_value ![z, L.weierstrassP z, L.derivWeierstrassP z, weierstrassZeta L z]
      1 (D.sigma z ^ 3)
      (D.sigma z ^ 3 * (L.derivWeierstrassP z * weierstrassZeta L z +
        2 * L.weierstrassP z ^ 2))

end MultiplicityCompactStep4

-- Assembly: WeierstrassEllipticZeta.nonzero_regularized_grid_zero_estimate
namespace MultiplicityCompactStep5
open _root_.WeierstrassEllipticZeta _root_.TranscendenceTheory

open WeierstrassEllipticZeta
open Filter
open scoped Topology

theorem _root_.WeierstrassEllipticZeta.nonzero_regularized_grid_zero_estimate
    (L : PeriodPair) (ω u₁ u₂ : ℂ)
    (h_grid : RegularAuxiliaryGridData L ω u₁ u₂)
    (D : EllipticSigmaDifferentialData L) :
    ∃ C : ℝ, 0 < C ∧ ∀ m l s q T : ℕ,
      1 ≤ m → 1 ≤ l → 1 ≤ s → 1 ≤ q → s ≤ q → l ≤ m → 3 ≤ T →
      3 * C * max ((m : ℝ) * (15 * l) ^ 2) ((q : ℝ) * (15 * l) ^ 2) <
        (T : ℝ) * (s : ℝ) ^ 2 * q →
      ∀ (c : Fin (m + 1) × Fin (l + 1) × Fin (l + 1) → ℂ) (G : ℂ → ℂ),
        AnalyticOnNhd ℂ G Set.univ →
        (∀ w : ℂ, w ∉ L.lattice → w + u₁ / 2 ∉ L.lattice →
          G w = D.sigma w ^ (15 * l) *
            (2 * (L.weierstrassP (u₁ / 2) - L.weierstrassP w)) ^ (3 * l) *
            (∑ i, c i * (w + u₁ / 2) ^ i.1.val *
              L.weierstrassP (w + u₁ / 2) ^ i.2.1.val *
              weierstrassZeta L (w + u₁ / 2) ^ i.2.2.val)) →
        G ≠ 0 → ∃ v ∈ auxiliaryGrid u₁ u₂ ω ![3 * s, 3 * s, 3 * q],
          ∃ n : ℕ, n ≤ T ∧ iteratedDeriv n G v ≠ 0 := by
  classical
  obtain ⟨C, hC, hzero⟩ := polynomial_regularized_grid_zero_estimate L ω u₁ u₂ h_grid D
  refine ⟨C, hC, ?_⟩
  intro m l s q T hm hl hs hq hsq hlm hT hineq c G hG hG_value hG_ne
  have hbase : u₁ / 2 ∉ L.lattice := by
    simpa [integerGridPoint] using h_grid.shifted_regular (fun _ => 0)
  obtain ⟨P, hP, hP_value⟩ := cleared_auxiliary_polynomial_presentation L (u₁ / 2) hbase m l c
  apply hzero m l s q T hm hl hs hq hsq hlm hT hineq P G hP hG ?_ hG_ne
  intro z hz
  let f : ℂ → Fin 4 → ℂ := fun w =>
    ![w, L.weierstrassP w, L.derivWeierstrassP w, weierstrassZeta L w]
  let R : ℂ → ℂ := fun w => D.sigma w ^ (15 * l) * MvPolynomial.eval (f w) P
  have hf : ContinuousAt f z := by
    apply continuousAt_pi.mpr
    intro i
    fin_cases i
    · change ContinuousAt id z
      exact continuousAt_id
    · simpa [f] using (L.analyticOnNhd_weierstrassP z hz).continuousAt
    · simpa [f] using (L.analyticOnNhd_derivWeierstrassP z hz).continuousAt
    · simpa [f] using (hasDerivAt_weierstrassZeta L z hz).continuousAt
  have hR : ContinuousAt R z :=
    (D.entire.continuous.continuousAt.pow _).mul
      ((MvPolynomial.continuous_eval P).continuousAt.comp hf)
  have hpunct : G =ᶠ[𝓝[≠] z] R := by
    have hreg : ∀ᶠ w in 𝓝 z, w ∉ L.lattice :=
      L.isClosed_lattice.isOpen_compl.mem_nhds hz
    have hshift : ∀ᶠ w in 𝓝 z,
        w + u₁ / 2 ∈ ((L.lattice : Set ℂ) \ {z + u₁ / 2})ᶜ :=
      (continuousAt_id.add continuousAt_const).eventually
        (L.compl_lattice_sdiff_singleton_mem_nhds (z + u₁ / 2))
    filter_upwards [hreg.filter_mono nhdsWithin_le_nhds,
      hshift.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with w hw hwshift hwz
    have hwv : w + u₁ / 2 ∉ L.lattice := by
      intro hwl
      exact hwshift ⟨hwl, fun he => hwz (add_right_cancel he)⟩
    dsimp only [R, f]
    rw [hP_value w hw hwv, hG_value w hw hwv, mul_assoc]
  exact ((hG z (Set.mem_univ z)).continuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE
    hR |>.mp hpunct).eq_of_nhds

end MultiplicityCompactStep5

-- Assembly: WeierstrassEllipticZeta.regular_grid_sigma_zero_estimate
namespace MultiplicityCompactStep6
open _root_.WeierstrassEllipticZeta _root_.TranscendenceTheory

open WeierstrassEllipticZeta

theorem _root_.WeierstrassEllipticZeta.regular_grid_sigma_zero_estimate
    (L : PeriodPair) (ω u₁ u₂ : ℂ)
    (h_grid : RegularAuxiliaryGridData L ω u₁ u₂)
    (D : EllipticSigmaDifferentialData L) :
    ∃ C : ℝ, 0 < C ∧ ∀ m l s q T : ℕ,
      1 ≤ m → 1 ≤ l → 1 ≤ s → 1 ≤ q → s ≤ q → l ≤ m → 3 ≤ T →
      3 * C * max ((m : ℝ) * (15 * l) ^ 2) ((q : ℝ) * (15 * l) ^ 2) <
        (T : ℝ) * (s : ℝ) ^ 2 * q →
      ∀ c : Fin (m + 1) × Fin (l + 1) × Fin (l + 1) → ℂ,
        c ≠ 0 → ∃ G : ℂ → ℂ, AnalyticOnNhd ℂ G Set.univ ∧
          (∀ w : ℂ, w ∉ L.lattice → w + u₁ / 2 ∉ L.lattice →
            G w = D.sigma w ^ (15 * l) *
              (2 * (L.weierstrassP (u₁ / 2) - L.weierstrassP w)) ^ (3 * l) *
              (∑ i, c i * (w + u₁ / 2) ^ i.1.val *
                L.weierstrassP (w + u₁ / 2) ^ i.2.1.val *
                weierstrassZeta L (w + u₁ / 2) ^ i.2.2.val)) ∧
          ∃ v ∈ auxiliaryGrid u₁ u₂ ω ![3 * s, 3 * s, 3 * q],
            ∃ n : ℕ, n ≤ T ∧ iteratedDeriv n G v ≠ 0 := by
  classical
  have hζ := hasDerivAt_weierstrassZeta L
  have hZ := zeta_addition_formula L
  have hP := wp_addition_formula L
  have hσne := (sigma_addition_from_differential L D hζ hZ).1
  have hσ : AnalyticOnNhd ℂ D.sigma Set.univ := fun z _ => D.entire.analyticAt z
  obtain ⟨S, hS, hS_value, _⟩ := sigma_regularized_coordinates_entire L D hζ
  have hbase : u₁ / 2 ∉ L.lattice := by
    simpa [integerGridPoint] using h_grid.shifted_regular (fun _ => 0)
  obtain ⟨C, hC, hzero⟩ := nonzero_regularized_grid_zero_estimate L ω u₁ u₂ h_grid D
  refine ⟨C, hC, ?_⟩
  intro m l s q T hm hl hs hq hsq hlm hT hineq c hc
  let F₀ : ℂ → ℂ := fun w => ∑ i, c i * w ^ i.1.val *
    L.weierstrassP w ^ i.2.1.val * weierstrassZeta L w ^ i.2.2.val
  let F : ℂ → ℂ := fun w => F₀ (w + u₁ / 2)
  have hZanalytic : AnalyticOnNhd ℂ (weierstrassZeta L) L.latticeᶜ :=
    (show DifferentiableOn ℂ (weierstrassZeta L) L.latticeᶜ from
      fun z hz => (hζ z hz).differentiableAt.differentiableWithinAt).analyticOnNhd
        L.isClosed_lattice.isOpen_compl
  have hF₀ (w : ℂ) (hw : w ∉ L.lattice) : AnalyticAt ℂ F₀ w := by
    apply Finset.analyticAt_fun_sum
    intro i hi
    exact (((analyticAt_const.mul (analyticAt_id.pow _)).mul
      ((L.analyticOnNhd_weierstrassP w hw).pow _)).mul ((hZanalytic w hw).pow _))
  have hF : ∀ w : ℂ, w + u₁ / 2 ∉ L.lattice → ContinuousAt F w := by
    intro w hw
    exact ((hF₀ _ hw).comp (f := fun w : ℂ => w + u₁ / 2)
      (show AnalyticAt ℂ (fun w : ℂ => w + u₁ / 2) w from
        analyticAt_id.add analyticAt_const)).continuousAt
  obtain ⟨G, hG, hG_value, _⟩ := cleared_addition_entire_growth_weighted
    L hZ hP D.sigma S hσ hS hS_value (u₁ / 2) hbase c
    (fun i => i.1.val) (fun i => i.2.1.val) (fun i => i.2.2.val) m l
    (fun i => by have := i.1.isLt; omega)
    (fun i => by have := i.2.1.isLt; omega)
    (fun i => by have := i.2.2.isLt; omega)
  have hGreg (w : ℂ) (hw : w ∉ L.lattice) (hwv : w + u₁ / 2 ∉ L.lattice) :
      G w = D.sigma w ^ (15 * l) *
        (2 * (L.weierstrassP (u₁ / 2) - L.weierstrassP w)) ^ (3 * l) * F w := by
    rw [hG_value w hw hwv, mul_assoc]
    congr 1
    dsimp only [F, F₀]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    dsimp [clearedAdditionMonomial]
    ring
  obtain ⟨w, hw, hFw⟩ := auxiliary_function_nonvanishing L m l c hc
  have hFne : ∃ z : ℂ, z + u₁ / 2 ∉ L.lattice ∧ F z ≠ 0 := by
    refine ⟨w - u₁ / 2, ?_, ?_⟩
    · simpa only [sub_add_cancel] using hw
    · simpa only [F, F₀, sub_add_cancel] using hFw
  have hGne := regularization_preserves_nonvanishing L (u₁ / 2) F D.sigma G
    (15 * l) l hF hσne hGreg hFne
  exact ⟨G, hG, hGreg, hzero m l s q T hm hl hs hq hsq hlm hT hineq c G hG hGreg hGne⟩

end MultiplicityCompactStep6

-- Assembly: WeierstrassEllipticZeta.regular_grid_polynomial_zero_estimate
namespace MultiplicityCompactStep7
open _root_.WeierstrassEllipticZeta _root_.TranscendenceTheory

open WeierstrassEllipticZeta

theorem _root_.WeierstrassEllipticZeta.regular_grid_polynomial_zero_estimate
    (L : PeriodPair) (ω u₁ u₂ : ℂ)
    (h_grid : RegularAuxiliaryGridData L ω u₁ u₂) :
    ∃ C : ℝ, 0 < C ∧ ∀ m l s q T : ℕ,
      1 ≤ m → 1 ≤ l → 1 ≤ s → 1 ≤ q → s ≤ q → l ≤ m → 3 ≤ T →
      3 * C * max ((m : ℝ) * (15 * l) ^ 2) ((q : ℝ) * (15 * l) ^ 2) <
        (T : ℝ) * (s : ℝ) ^ 2 * q →
      ∀ c : Fin (m + 1) × Fin (l + 1) × Fin (l + 1) → ℂ,
        c ≠ 0 → ∃ v ∈ auxiliaryGrid u₁ u₂ ω ![3 * s, 3 * s, 3 * q],
          ∃ n : ℕ, n ≤ T + 6 * l ∧
            iteratedDeriv n (fun w => ∑ i, c i * w ^ i.1.val *
              L.weierstrassP w ^ i.2.1.val * weierstrassZeta L w ^ i.2.2.val)
                (u₁ / 2 + v) ≠ 0 := by
  classical
  obtain ⟨D⟩ := exists_elliptic_sigma_differential_data L
  have hζ := hasDerivAt_weierstrassZeta L
  obtain ⟨S, hS, hS_value, _⟩ := sigma_regularized_coordinates_entire L D hζ
  obtain ⟨C, hC, hzero⟩ := regular_grid_sigma_zero_estimate L ω u₁ u₂ h_grid D
  refine ⟨C, hC, ?_⟩
  intro m l s q T hm hl hs hq hsq hlm hT hineq c hc
  obtain ⟨G, hG, hG_value, v, hv, t, ht, hnonzero⟩ :=
    hzero m l s q T hm hl hs hq hsq hlm hT hineq c hc
  let F₀ : ℂ → ℂ := fun w => ∑ i, c i * w ^ i.1.val *
    L.weierstrassP w ^ i.2.1.val * weierstrassZeta L w ^ i.2.2.val
  let F : ℂ → ℂ := fun w => F₀ (w + u₁ / 2)
  have hZ : AnalyticOnNhd ℂ (weierstrassZeta L) L.latticeᶜ :=
    (show DifferentiableOn ℂ (weierstrassZeta L) L.latticeᶜ from
      fun z hz => (hζ z hz).differentiableAt.differentiableWithinAt).analyticOnNhd
        L.isClosed_lattice.isOpen_compl
  have hF₀ (w : ℂ) (hw : w ∉ L.lattice) : AnalyticAt ℂ F₀ w := by
    apply Finset.analyticAt_fun_sum
    intro i hi
    exact (((analyticAt_const.mul (analyticAt_id.pow _)).mul
      ((L.analyticOnNhd_weierstrassP w hw).pow _)).mul ((hZ w hw).pow _))
  have hF : AnalyticOnNhd ℂ F {w : ℂ | w + u₁ / 2 ∉ L.lattice} := by
    intro w hw
    exact (hF₀ _ hw).comp (f := fun w : ℂ => w + u₁ / 2)
      (show AnalyticAt ℂ (fun w : ℂ => w + u₁ / 2) w from
        analyticAt_id.add analyticAt_const)
  have hσ : AnalyticOnNhd ℂ D.sigma Set.univ := fun w _ => D.entire.analyticAt w
  have hS₁ : ∀ w : ℂ, w ∉ L.lattice → S 1 w = D.sigma w ^ 2 * L.weierstrassP w := by
    intro w hw
    simpa [ellipticPoleCoordinates] using hS_value w hw 1
  have hvreg : v + u₁ / 2 ∉ L.lattice :=
    h_grid.shifted_grid_regular ![3 * s, 3 * s, 3 * q] (v + u₁ / 2)
      (Finset.mem_image.mpr ⟨v, hv, rfl⟩)
  obtain ⟨n, hn, hFn⟩ := regularized_nonzero_derivative_transfer L (u₁ / 2)
    F D.sigma (S 1) G (15 * l) l (by omega) hF hσ (hS 1) hG hS₁ hG_value
    v hvreg t hnonzero
  refine ⟨v, hv, n, hn.trans (ht.trans (Nat.le_add_right T (6 * l))), ?_⟩
  simpa only [F, iteratedDeriv_comp_add_const, add_comm v (u₁ / 2)] using hFn

end MultiplicityCompactStep7

-- Assembly: WeierstrassEllipticZeta.auxiliary_grid_bounded_nonzero_derivative
namespace MultiplicityCompactStep8
open _root_.WeierstrassEllipticZeta _root_.TranscendenceTheory

open scoped Polynomial
open Filter WeierstrassEllipticZeta

theorem _root_.WeierstrassEllipticZeta.auxiliary_grid_bounded_nonzero_derivative
    (L : PeriodPair) (ω u₁ u₂ : ℂ)
    (h_grid : RegularAuxiliaryGridData L ω u₁ u₂) :
    ∃ K : ℕ, 1 ≤ K ∧ ∀ᶠ N : ℕ in Filter.atTop,
      let m := auxiliaryL0 N
      let l := auxiliaryL N
      ∀ c : Fin (m + 1) × Fin (l + 1) × Fin (l + 1) → ℂ,
        c ≠ 0 → ∃ v ∈ auxiliaryGrid u₁ u₂ ω
          ![3 * auxiliaryS N, 3 * auxiliaryS N, 3 * auxiliaryS3 N],
          ∃ n : ℕ, n ≤ K * m ∧
            iteratedDeriv n (fun w => ∑ i, c i * w ^ i.1.val *
              L.weierstrassP w ^ i.2.1.val * weierstrassZeta L w ^ i.2.2.val)
                (u₁ / 2 + v) ≠ 0 := by
  obtain ⟨C, hC, hzero⟩ := regular_grid_polynomial_zero_estimate L ω u₁ u₂ h_grid
  obtain ⟨k, hk, hparameters⟩ := auxiliary_zero_estimate_parameter_bounds C hC
  refine ⟨k + 6, by omega, ?_⟩
  filter_upwards [hparameters] with N hN
  rcases hN with ⟨hm, hl, hs, hq, hsq, _, hlm, hT, hineq⟩
  dsimp only
  intro c hc
  obtain ⟨v, hv, n, hn, hnonzero⟩ := hzero (auxiliaryL0 N) (auxiliaryL N)
    (auxiliaryS N) (auxiliaryS3 N) (k * auxiliaryL0 N)
    hm hl hs hq hsq hlm hT hineq c hc
  refine ⟨v, hv, n, hn.trans ?_, hnonzero⟩
  calc
    k * auxiliaryL0 N + 6 * auxiliaryL N ≤
        k * auxiliaryL0 N + 6 * auxiliaryL0 N :=
      Nat.add_le_add_left (Nat.mul_le_mul_left 6 hlm) _
    _ = (k + 6) * auxiliaryL0 N := by ring

end MultiplicityCompactStep8

-- Assembly: WeierstrassEllipticZeta.exists_complex_auxiliary_systems_on_regular_grids
namespace MultiplicityCompactStep9
open _root_.WeierstrassEllipticZeta _root_.TranscendenceTheory

noncomputable section
set_option maxHeartbeats 1000000
open WeierstrassEllipticZeta MvPolynomial Filter
open scoped Polynomial Topology
namespace WeierstrassEllipticZeta

-- Retained proved helper calculations: on_regular_grids
set_option maxHeartbeats 600000

open MvPolynomial Filter
open scoped Topology


private lemma p2m_mc_0_degree_neg (p : MvPolynomial (Fin 8) ℤ) :
    (-p).totalDegree = p.totalDegree := by simp [totalDegree]

private lemma p2m_mc_0_jet_derivation_degree (i : Fin 8) :
    (ellipticJetDerivation (X i)).totalDegree ≤ 2 := by
  fin_cases i <;> simp [ellipticJetDerivation]
  have h₁ := totalDegree_mul (12 * X 5 : MvPolynomial (Fin 8) ℤ) (X 6)
  have h₂ := totalDegree_mul (C (12 : ℤ) : MvPolynomial (Fin 8) ℤ) (X 5)
  change (12 * X 5 : MvPolynomial (Fin 8) ℤ).totalDegree ≤ _ at h₂
  simp only [totalDegree_C, totalDegree_X] at h₁ h₂
  have hc : (12 : MvPolynomial (Fin 8) ℤ).totalDegree = 0 := totalDegree_C (12 : ℤ)
  omega

private lemma p2m_mc_0_degree_sub (p q : MvPolynomial (Fin 8) ℤ) :
    (p - q).totalDegree ≤ max p.totalDegree q.totalDegree := by
  simpa [sub_eq_add_neg, p2m_mc_0_degree_neg] using totalDegree_add p (-q)

private lemma p2m_mc_0_cleared_polynomial_degree (M l₀ l₂ l₃ : ℕ)
    (h₂ : l₂ ≤ M) (h₃ : l₃ ≤ M) :
    (clearedAdditionPolynomial M l₀ l₂ l₃).totalDegree ≤ l₀ + 5 * M := by
  have hdiff (i j : Fin 8) : (X i - X j : MvPolynomial (Fin 8) ℤ).totalDegree ≤ 1 := by
    simpa using p2m_mc_0_degree_sub (X i) (X j)
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

private lemma p2m_mc_0_jet_coordinates_ode (L : PeriodPair)
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

private lemma p2m_mc_0_cleared_monomial_eq (L : PeriodPair) (M l₀ l₂ l₃ : ℕ)
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

private theorem p2m_mc_0_cleared_addition_jet_data (L : PeriodPair)
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
  have hpoly := p2m_mc_0_cleared_polynomial_degree M l₀ l₂ l₃ h₂ h₃
  have hjet (v : ℂ) := TranscendenceTheory.polynomial_ode_iterated_deriv
    ellipticJetDerivation p2m_mc_0_jet_derivation_degree (L.lattice : Set ℂ)ᶜ
    L.isClosed_lattice.isOpen_compl (fun i w => ellipticJetCoordinates L v w i)
    (fun z hz i => p2m_mc_0_jet_coordinates_ode L hzeta v z hz i)
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
    exact p2m_mc_0_cleared_monomial_eq L M l₀ l₂ l₃ h₂ h₃ v w
      (hZ w v hw hv hwv) (hP w v hw hv hwv)
  rw [heq.iteratedDeriv_eq]
  exact (hjet v).2 z hz


open WeierstrassEllipticZeta
open scoped Polynomial


-- Retained proved helper calculations: from_polynomial_jets
open MvPolynomial


private def p2m_mc_1_polyLength {σ : Type} (p : MvPolynomial σ ℤ) : ℕ :=
  ∑ m ∈ p.support, (p.coeff m).natAbs

private lemma p2m_mc_1_polyLength_eq {σ : Type} (p : MvPolynomial σ ℤ) :
    p2m_mc_1_polyLength p = ∑ m ∈ p.support, (p.coeff m).natAbs := rfl

private lemma p2m_mc_1_polyLength_sum_le {σ ι : Type} (s : Finset ι)
    (f : ι → MvPolynomial σ ℤ) :
    p2m_mc_1_polyLength (∑ i ∈ s, f i) ≤ ∑ i ∈ s, p2m_mc_1_polyLength (f i) := by
  classical
  let t := s.biUnion fun i => (f i).support
  have heq (p : MvPolynomial σ ℤ) (hp : p.support ⊆ t) :
      p2m_mc_1_polyLength p = ∑ m ∈ t, (p.coeff m).natAbs := by
    rw [p2m_mc_1_polyLength_eq]
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
    _ = ∑ i ∈ s, p2m_mc_1_polyLength (f i) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      exact (heq _ (Finset.subset_biUnion_of_mem (fun i => (f i).support) hi)).symm

private lemma p2m_mc_1_polyLength_monomial {σ : Type} (m : σ →₀ ℕ) (a : ℤ) :
    p2m_mc_1_polyLength (monomial m a) = a.natAbs := by
  classical
  by_cases ha : a = 0 <;> simp [p2m_mc_1_polyLength, support_monomial, ha]

private lemma p2m_mc_1_polyLength_add {σ : Type} (p q : MvPolynomial σ ℤ) :
    p2m_mc_1_polyLength (p + q) ≤ p2m_mc_1_polyLength p + p2m_mc_1_polyLength q := by
  simpa [Fin.sum_univ_two] using
    p2m_mc_1_polyLength_sum_le Finset.univ ![p, q]

private lemma p2m_mc_1_polyLength_mul {σ : Type} (p q : MvPolynomial σ ℤ) :
    p2m_mc_1_polyLength (p * q) ≤ p2m_mc_1_polyLength p * p2m_mc_1_polyLength q := by
  classical
  conv_lhs => rw [p.as_sum, q.as_sum]
  simp only [Finset.sum_mul, Finset.mul_sum, monomial_mul]
  apply (p2m_mc_1_polyLength_sum_le _ _).trans
  apply (Finset.sum_le_sum fun _ _ => p2m_mc_1_polyLength_sum_le _ _).trans
  simp only [p2m_mc_1_polyLength_monomial, Int.natAbs_mul]
  simp only [← Finset.mul_sum, ← Finset.sum_mul, ← p2m_mc_1_polyLength_eq, le_refl]

private lemma p2m_mc_1_polyLength_pow {σ : Type} (p : MvPolynomial σ ℤ) (n : ℕ) :
    p2m_mc_1_polyLength (p ^ n) ≤ p2m_mc_1_polyLength p ^ n := by
  induction n with
  | zero =>
    change p2m_mc_1_polyLength (monomial (0 : σ →₀ ℕ) 1) ≤ 1
    exact (p2m_mc_1_polyLength_monomial _ _).le
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact (p2m_mc_1_polyLength_mul _ _).trans (Nat.mul_le_mul_right _ ih)

private lemma p2m_mc_1_coeff_le_polyLength {σ : Type} (p : MvPolynomial σ ℤ) (m : σ →₀ ℕ) :
    (p.coeff m).natAbs ≤ p2m_mc_1_polyLength p := by
  classical
  by_cases hm : m ∈ p.support
  · rw [p2m_mc_1_polyLength_eq]
    exact Finset.single_le_sum (f := fun m => (p.coeff m).natAbs) (fun _ _ => Nat.zero_le _) hm
  · simp [notMem_support_iff.mp hm]

private lemma p2m_mc_1_degree_neg (p : MvPolynomial (Fin 8) ℤ) :
    (-p).totalDegree = p.totalDegree := by simp [totalDegree]

private lemma p2m_mc_1_jet_derivation_degree (i : Fin 8) :
    (ellipticJetDerivation (X i)).totalDegree ≤ 2 := by
  fin_cases i <;> simp [ellipticJetDerivation]
  have h₁ := totalDegree_mul (12 * X 5 : MvPolynomial (Fin 8) ℤ) (X 6)
  have h₂ := totalDegree_mul (C (12 : ℤ) : MvPolynomial (Fin 8) ℤ) (X 5)
  change (12 * X 5 : MvPolynomial (Fin 8) ℤ).totalDegree ≤ _ at h₂
  simp only [totalDegree_C, totalDegree_X] at h₁ h₂
  have hc : (12 : MvPolynomial (Fin 8) ℤ).totalDegree = 0 := totalDegree_C (12 : ℤ)
  omega

private lemma p2m_mc_1_degree_sub (p q : MvPolynomial (Fin 8) ℤ) :
    (p - q).totalDegree ≤ max p.totalDegree q.totalDegree := by
  simpa [sub_eq_add_neg, p2m_mc_1_degree_neg] using totalDegree_add p (-q)

private lemma p2m_mc_1_cleared_polynomial_degree (M l₀ l₂ l₃ : ℕ)
    (h₂ : l₂ ≤ M) (h₃ : l₃ ≤ M) :
    (clearedAdditionPolynomial M l₀ l₂ l₃).totalDegree ≤ l₀ + 5 * M := by
  have hdiff (i j : Fin 8) : (X i - X j : MvPolynomial (Fin 8) ℤ).totalDegree ≤ 1 := by
    simpa using p2m_mc_1_degree_sub (X i) (X j)
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


private lemma p2m_mc_1_polyLength_C (a : ℤ) :
    p2m_mc_1_polyLength (C a : MvPolynomial (Fin 8) ℤ) = a.natAbs :=
  p2m_mc_1_polyLength_monomial 0 a

private lemma p2m_mc_1_polyLength_X (i : Fin 8) :
    p2m_mc_1_polyLength (X i : MvPolynomial (Fin 8) ℤ) = 1 :=
  p2m_mc_1_polyLength_monomial _ 1

private lemma p2m_mc_1_polyLength_neg (p : MvPolynomial (Fin 8) ℤ) :
    p2m_mc_1_polyLength (-p) = p2m_mc_1_polyLength p := by simp [p2m_mc_1_polyLength]

private lemma p2m_mc_1_length_mul_le {p q : MvPolynomial (Fin 8) ℤ} {a b : ℕ}
    (hp : p2m_mc_1_polyLength p ≤ a) (hq : p2m_mc_1_polyLength q ≤ b) :
    p2m_mc_1_polyLength (p * q) ≤ a * b :=
  (p2m_mc_1_polyLength_mul p q).trans (Nat.mul_le_mul hp hq)

private lemma p2m_mc_1_length_pow_le {p : MvPolynomial (Fin 8) ℤ} {a : ℕ}
    (hp : p2m_mc_1_polyLength p ≤ a) (n : ℕ) : p2m_mc_1_polyLength (p ^ n) ≤ a ^ n :=
  (p2m_mc_1_polyLength_pow p n).trans (Nat.pow_le_pow_left hp n)

private lemma p2m_mc_1_jet_derivation_length (i : Fin 8) :
    p2m_mc_1_polyLength (ellipticJetDerivation (X i)) ≤ 12 := by
  have h0 : p2m_mc_1_polyLength (0 : MvPolynomial (Fin 8) ℤ) = 0 := by simpa using p2m_mc_1_polyLength_C 0
  have h1 : p2m_mc_1_polyLength (1 : MvPolynomial (Fin 8) ℤ) = 1 := p2m_mc_1_polyLength_C 1
  fin_cases i <;> simp [ellipticJetDerivation, p2m_mc_1_polyLength_X, p2m_mc_1_polyLength_neg, h0, h1]
  simpa using p2m_mc_1_length_mul_le
    (p2m_mc_1_length_mul_le (p2m_mc_1_polyLength_C 12).le (p2m_mc_1_polyLength_X 5).le) (p2m_mc_1_polyLength_X 6).le

private lemma p2m_mc_1_cleared_polynomial_length (M l₀ l₂ l₃ : ℕ)
    (h₂ : l₂ ≤ M) (h₃ : l₃ ≤ M) :
    p2m_mc_1_polyLength (clearedAdditionPolynomial M l₀ l₂ l₃) ≤ 23040 ^ M := by
  have hs (i j : Fin 8) : p2m_mc_1_polyLength (X i + X j : MvPolynomial (Fin 8) ℤ) ≤ 2 := by
    simpa [p2m_mc_1_polyLength_X] using p2m_mc_1_polyLength_add (X i) (X j)
  have hd (i j : Fin 8) : p2m_mc_1_polyLength (X i - X j : MvPolynomial (Fin 8) ℤ) ≤ 2 := by
    simpa [sub_eq_add_neg, p2m_mc_1_polyLength_X, p2m_mc_1_polyLength_neg] using p2m_mc_1_polyLength_add (X i) (-X j)
  have hA : p2m_mc_1_polyLength (2 * (X 2 - X 5) : MvPolynomial (Fin 8) ℤ) ≤ 4 :=
    p2m_mc_1_length_mul_le (p2m_mc_1_polyLength_C 2).le (hd 2 5)
  have hB : p2m_mc_1_polyLength (-4 * (X 5 + X 2) * (X 2 - X 5) ^ 2 +
      (X 3 - X 6) ^ 2 : MvPolynomial (Fin 8) ℤ) ≤ 36 := by
    apply (p2m_mc_1_polyLength_add _ _).trans
    have hc : p2m_mc_1_polyLength (-4 : MvPolynomial (Fin 8) ℤ) ≤ 4 := by
      simpa using (p2m_mc_1_polyLength_C (-4)).le
    exact Nat.add_le_add (p2m_mc_1_length_mul_le (p2m_mc_1_length_mul_le hc (hs 5 2))
      (p2m_mc_1_length_pow_le (hd 2 5) 2)) (p2m_mc_1_length_pow_le (hd 3 6) 2)
  have hC : p2m_mc_1_polyLength (2 * (X 4 + X 1) * (X 2 - X 5) + (X 3 - X 6) :
      MvPolynomial (Fin 8) ℤ) ≤ 10 := by
    exact (p2m_mc_1_polyLength_add _ _).trans (Nat.add_le_add
      (p2m_mc_1_length_mul_le (p2m_mc_1_length_mul_le (p2m_mc_1_polyLength_C 2).le (hs 4 1)) (hd 2 5)) (hd 3 6))
  unfold clearedAdditionPolynomial
  calc
    _ ≤ 1 ^ l₀ * 4 ^ (3 * M - 2 * l₂ - l₃) * 36 ^ l₂ * 10 ^ l₃ :=
      p2m_mc_1_length_mul_le (p2m_mc_1_length_mul_le (p2m_mc_1_length_mul_le
        (p2m_mc_1_length_pow_le (p2m_mc_1_polyLength_X 0).le l₀) (p2m_mc_1_length_pow_le hA _))
        (p2m_mc_1_length_pow_le hB _)) (p2m_mc_1_length_pow_le hC _)
    _ ≤ 4 ^ (3 * M) * 36 ^ M * 10 ^ M := by
      simp only [one_pow, one_mul]
      gcongr <;> omega
    _ = _ := by rw [pow_mul, ← mul_pow, ← mul_pow]; norm_num

private theorem p2m_mc_1_cleared_addition_height (M l₀ l₂ l₃ : ℕ)
    (h₂ : l₂ ≤ M) (h₃ : l₃ ≤ M) (n : ℕ) :
    (∑ m ∈ (ellipticJetDerivation^[n] (clearedAdditionPolynomial M l₀ l₂ l₃)).support,
      ((ellipticJetDerivation^[n] (clearedAdditionPolynomial M l₀ l₂ l₃)).coeff m).natAbs) ≤
      n.factorial * 2 ^ (41 * (l₀ + M + n)) := by
  have h := (TranscendenceTheory.polynomial_derivation_length_bound
    ellipticJetDerivation p2m_mc_1_jet_derivation_degree 12 (by omega) p2m_mc_1_jet_derivation_length
    (clearedAdditionPolynomial M l₀ l₂ l₃) n).2
  change p2m_mc_1_polyLength _ ≤ _ at h ⊢
  have hlen := p2m_mc_1_cleared_polynomial_length M l₀ l₂ l₃ h₂ h₃
  have hdeg := p2m_mc_1_cleared_polynomial_degree M l₀ l₂ l₃ h₂ h₃
  apply h.trans
  change p2m_mc_1_polyLength (clearedAdditionPolynomial M l₀ l₂ l₃) * n.factorial *
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


open WeierstrassEllipticZeta
open scoped Polynomial


-- Retained proved helper calculations: from_bounded_polynomial_jets
open MvPolynomial


private lemma p2m_mc_2_pderiv_degreeOf_le {σ : Type} (p : MvPolynomial σ ℤ) (i j : σ) :
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

private lemma p2m_mc_2_derivation_sum_apply {σ : Type} [Fintype σ]
    (F : σ → Derivation ℤ (MvPolynomial σ ℤ) (MvPolynomial σ ℤ))
    (p : MvPolynomial σ ℤ) : (∑ i, F i) p = ∑ i, F i p := by
  change (Derivation.coeFnAddMonoidHom (∑ i, F i)) p = _
  rw [map_sum, Finset.sum_apply]
  rfl

private lemma p2m_mc_2_derivation_degreeOf_le {σ : Type} [Fintype σ]
    (D : Derivation ℤ (MvPolynomial σ ℤ) (MvPolynomial σ ℤ))
    (i : σ) (hD : ∀ j, (D (X j)).degreeOf i = 0) (p : MvPolynomial σ ℤ) :
    (D p).degreeOf i ≤ p.degreeOf i := by
  classical
  have hrepr : D = ∑ j, D (X j) • pderiv j := by
    apply MvPolynomial.derivation_ext
    intro j
    simp [p2m_mc_2_derivation_sum_apply, Derivation.smul_apply, Pi.single_apply]
  have hvalue : D p = ∑ j, D (X j) * pderiv j p := by
    conv_lhs => rw [hrepr]
    simp [p2m_mc_2_derivation_sum_apply]
  rw [hvalue]
  apply (degreeOf_sum_le _ _ _).trans
  apply Finset.sup_le
  intro j _
  simpa only [hD j, zero_add] using
    (degreeOf_mul_le i (D (X j)) (pderiv j p)).trans
      (Nat.add_le_add_left (p2m_mc_2_pderiv_degreeOf_le p i j) _)

private lemma p2m_mc_2_jet_fixed_degree (i : Fin 8) (hi : i.val < 4)
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
    exact (p2m_mc_2_derivation_degreeOf_le ellipticJetDerivation i hD _).trans ih

private lemma p2m_mc_2_cleared_polynomial_degree_zero (M l₂ l₃ : ℕ) :
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

private lemma p2m_mc_2_jet_coordinate_degrees (L : PeriodPair) (h_jets : ClearedAdditionJetData L)
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
    apply (p2m_mc_2_jet_fixed_degree 0 (by decide) _ n).trans
    rw [hrepr]
    apply (degreeOf_mul_le _ _ _).trans
    simpa [p2m_mc_2_cleared_polynomial_degree_zero] using h₀
  have hfixed (i : Fin 8) (hi : i.val < 4) (hi0 : i ≠ 0) :
      (ellipticJetDerivation^[n] (clearedAdditionPolynomial M l₀ l₂ l₃)).degreeOf i ≤ 5 * M := by
    apply (p2m_mc_2_jet_fixed_degree i hi _ n).trans
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

private theorem p2m_mc_2_arithmetic_jets_of_polynomial_jets (L : PeriodPair)
    (h_jets : ClearedAdditionJetData L)
    (h_height : ∀ (M l₀ l₂ l₃ : ℕ), l₂ ≤ M → l₃ ≤ M → ∀ n : ℕ,
      (∑ m ∈ (ellipticJetDerivation^[n] (clearedAdditionPolynomial M l₀ l₂ l₃)).support,
        ((ellipticJetDerivation^[n] (clearedAdditionPolynomial M l₀ l₂ l₃)).coeff m).natAbs) ≤
        n.factorial * 2 ^ (41 * (l₀ + M + n))) : ArithmeticJetData L := by
  intro M L₀ l₀ l₂ l₃ n h₀ h₂ h₃ k s q d H hsdeg hqdeg hslen hqlen
  obtain ⟨r, hrdeg, hrlen, hreval⟩ :=
    TranscendenceTheory.polynomial_clear_denominators_bound (A := ℂ)
      (ellipticJetDerivation^[n] (clearedAdditionPolynomial M l₀ l₂ l₃))
      k d H s q (p2m_mc_2_jet_coordinate_degrees L h_jets M L₀ l₀ l₂ l₃ n h₀ h₂ h₃)
      hsdeg hqdeg hslen hqlen
  refine ⟨r, hrdeg, hrlen.trans ?_, ?_⟩
  · apply Nat.mul_le_mul_right
    apply (h_height M l₀ l₂ l₃ h₂ h₃ n).trans
    apply Nat.mul_le_mul_left
    exact Nat.pow_le_pow_right (by omega) (by omega)
  · intro w v z hv hz hvz hvalues
    rw [(h_jets M l₀ l₂ l₃ h₂ h₃ n).2 v z hv hz hvz]
    exact hreval (eval₂Hom (Int.castRingHom ℂ) w) (ellipticJetCoordinates L v z) hvalues


open WeierstrassEllipticZeta
open scoped Polynomial


-- Retained proved helper calculations: from_arithmetic_jets
open scoped Polynomial


private theorem p2m_mc_3_reduced_arithmetic_jets_of_arithmetic_jets (L : PeriodPair)
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


open WeierstrassEllipticZeta


-- Retained proved helper calculations: from_reduced_arithmetic_jets
open scoped Polynomial


private theorem p2m_mc_4_reduced_jet_systems_of_reduced_jets
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


open WeierstrassEllipticZeta


-- Retained proved helper calculations: from_reduced_jet_systems
open scoped Topology
open Filter Metric Set


private theorem p2m_mc_5_grid_interpolation_of_regular_grid (L : PeriodPair) (ω u₁ u₂ : ℂ)
    (h_grid : RegularAuxiliaryGridData L ω u₁ u₂) :
    AuxiliaryGridInterpolationData ω u₁ u₂ := by
  intro A T f G ψ hG hf hψ hGf hjet r R C hr hrR hrad hC
  have hzero : ∀ x ∈ shiftedAuxiliaryGrid u₁ u₂ ω A,
      ∀ j < T, iteratedDeriv j G x = 0 := by
    intro x hx
    apply (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (hG x trivial)).1
    have hfT := (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (hf x hx)).2
      (hjet x hx)
    rw [analyticOrderAt_congr (hGf x hx)]
    change (T : ℕ∞) ≤ analyticOrderAt (ψ * f) x
    rw [analyticOrderAt_mul (hψ x hx) (hf x hx)]
    exact hfT.trans le_add_self
  have hsmall := TranscendenceTheory.finite_zeros_derivative_bound G hG
    (shiftedAuxiliaryGrid u₁ u₂ ω A) (fun _ => T) hzero r R C hr hrR
    (fun x hx => (h_grid.shifted_grid_radius A x hx).trans hrad) hC
  simpa [Finset.sum_const_nat, h_grid.card_shifted_grid, mul_comm] using hsmall


open scoped Polynomial
open WeierstrassEllipticZeta


-- Retained proved helper calculations: from_interpolating_jets
open Filter Metric Set
open scoped Topology


private theorem p2m_mc_6_elliptic_regularization_of_interpolation (L : PeriodPair) (ω u₁ u₂ : ℂ)
    (h_grid : RegularAuxiliaryGridData L ω u₁ u₂)
    (hzeta : ∀ z : ℂ, z ∉ L.lattice →
      HasDerivAt (weierstrassZeta L) (-L.weierstrassP z) z)
    (h_interpolation : AuxiliaryGridInterpolationData ω u₁ u₂) :
    EllipticRegularizationData L ω u₁ u₂ := by
  intro σ S hσ hS hrel ι _ v c l e D K hl he
  have hweight (i : ι) : ∑ j : Fin 3, (j.val + 1) * e i j ≤ K := by
    simpa [Fin.sum_univ_succ, add_assoc] using he i
  obtain ⟨G, hG, hEq, hbound⟩ :=
    TranscendenceTheory.exists_entire_monomial_regularization
      (L.lattice : Set ℂ)ᶜ σ (fun j z => ellipticPoleCoordinates L z j) S
      hσ hS (fun j => j.val + 1) (fun j => by omega) hrel v c l e D K hl hweight
  refine ⟨G, hG, hEq, hbound, ?_⟩
  intro A T r R B hr hR hB hrad hbasic hjets
  have hZ : AnalyticOnNhd ℂ (weierstrassZeta L) (L.lattice : Set ℂ)ᶜ :=
    (show DifferentiableOn ℂ (weierstrassZeta L) (L.lattice : Set ℂ)ᶜ from
      fun z hz => (hzeta z hz).differentiableAt.differentiableWithinAt).analyticOnNhd
        L.isClosed_lattice.isOpen_compl
  have hφ (z : ℂ) (hz : z ∉ L.lattice) (j : Fin 3) :
      AnalyticAt ℂ (fun z => ellipticPoleCoordinates L z j) z := by
    fin_cases j
    · exact hZ z hz
    · exact L.analyticOnNhd_weierstrassP z hz
    · exact L.analyticOnNhd_derivWeierstrassP z hz
  have hf (z : ℂ) (hz : z ∉ L.lattice) :
      AnalyticAt ℂ (ellipticRegularizationSum L v c l e) z := by
    apply Finset.analyticAt_fun_sum
    intro i _
    exact (analyticAt_const.mul ((analyticAt_id.add analyticAt_const).pow _)).mul
      (Finset.analyticAt_fun_prod _ fun j _ => (hφ z hz j).pow _)
  have hlocal (x : ℂ) (hx : x ∈ shiftedAuxiliaryGrid u₁ u₂ ω A) :
      G =ᶠ[𝓝 x] fun z => σ z ^ K * ellipticRegularizationSum L v c l e z := by
    filter_upwards [L.isClosed_lattice.isOpen_compl.mem_nhds
      (h_grid.shifted_grid_regular A x hx)] with z hz
    exact hEq z hz
  exact h_interpolation A T (ellipticRegularizationSum L v c l e) G
    (fun z => σ z ^ K) hG
    (fun x hx => hf x (h_grid.shifted_grid_regular A x hx))
    (fun x _ => (hσ x trivial).pow K) hlocal hjets r R
    ((∑ i, ‖c i‖) * (max 1 (R + ‖v‖)) ^ D * B ^ K)
    hr hR hrad (fun z hz => hbound R B hB hbasic z (by
      simpa only [mem_sphere, dist_zero_right] using le_of_eq hz))


open scoped Polynomial
open WeierstrassEllipticZeta


-- Retained proved helper calculations: from_entire_regularization
open Filter Metric Set
open scoped Topology


private theorem p2m_mc_7_cleared_addition_entire_data (L : PeriodPair) (ω u₁ u₂ : ℂ)
    (h_grid : RegularAuxiliaryGridData L ω u₁ u₂)
    (hzeta : ∀ z : ℂ, z ∉ L.lattice →
      HasDerivAt (weierstrassZeta L) (-L.weierstrassP z) z)
    (hZ : ∀ z v : ℂ, z ∉ L.lattice → v ∉ L.lattice → z + v ∉ L.lattice →
      2 * (L.weierstrassP v - L.weierstrassP z) * weierstrassZeta L (z + v) =
        2 * (weierstrassZeta L z + weierstrassZeta L v) *
          (L.weierstrassP v - L.weierstrassP z) +
        L.derivWeierstrassP v - L.derivWeierstrassP z)
    (hP : ∀ z v : ℂ, z ∉ L.lattice → v ∉ L.lattice → z + v ∉ L.lattice →
      4 * (L.weierstrassP v - L.weierstrassP z) ^ 2 * L.weierstrassP (z + v) =
        -4 * (L.weierstrassP z + L.weierstrassP v) *
          (L.weierstrassP v - L.weierstrassP z) ^ 2 +
        (L.derivWeierstrassP v - L.derivWeierstrassP z) ^ 2)
    (h_interpolation : AuxiliaryGridInterpolationData ω u₁ u₂) :
    ClearedAdditionEntireData L ω u₁ u₂ := by
  intro σ S hσ hS hrel ι _ v hv c l₀ l₂ l₃ D M h₀ h₂ h₃
  obtain ⟨G, hG, hEq, hbound⟩ := cleared_addition_entire_growth L hZ hP σ S hσ hS hrel
    v hv c l₀ l₂ l₃ D M h₀ h₂ h₃
  refine ⟨G, hG, hEq, hbound, ?_⟩
  intro A T r R B hr hR hB hrad hbasic hshift hjets
  have hZan : AnalyticOnNhd ℂ (weierstrassZeta L) (L.lattice : Set ℂ)ᶜ :=
    (show DifferentiableOn ℂ (weierstrassZeta L) (L.lattice : Set ℂ)ᶜ from
      fun z hz => (hzeta z hz).differentiableAt.differentiableWithinAt).analyticOnNhd
        L.isClosed_lattice.isOpen_compl
  have hf (x : ℂ) (hx : x ∈ shiftedAuxiliaryGrid u₁ u₂ ω A) :
      AnalyticAt ℂ (clearedAuxiliarySum L v c l₀ l₂ l₃ M) x := by
    have hPx := L.analyticOnNhd_weierstrassP x (h_grid.shifted_grid_regular A x hx)
    have hadd : AnalyticAt ℂ (fun z => z + v) x := analyticAt_id.add analyticAt_const
    have hPv : AnalyticAt ℂ (fun z => L.weierstrassP (z + v)) x :=
      (L.analyticOnNhd_weierstrassP (x + v) (hshift x hx)).comp
        (f := fun z : ℂ => z + v) (x := x) hadd
    have hZv : AnalyticAt ℂ (fun z => weierstrassZeta L (z + v)) x :=
      (hZan (x + v) (hshift x hx)).comp (f := fun z : ℂ => z + v) (x := x) hadd
    unfold clearedAuxiliarySum
    apply Finset.analyticAt_fun_sum
    intro i _
    apply analyticAt_const.mul
    unfold clearedAdditionMonomial
    fun_prop
  have hlocal (x : ℂ) (hx : x ∈ shiftedAuxiliaryGrid u₁ u₂ ω A) :
      G =ᶠ[𝓝 x] fun z => σ z ^ (15 * M) * clearedAuxiliarySum L v c l₀ l₂ l₃ M z := by
    have hnear : ∀ᶠ z in 𝓝 x, z + v ∉ L.lattice :=
      (continuousAt_id.add_const v).eventually
        (L.isClosed_lattice.isOpen_compl.mem_nhds (hshift x hx))
    filter_upwards [L.isClosed_lattice.isOpen_compl.mem_nhds
      (h_grid.shifted_grid_regular A x hx), hnear] with z hz hzv
    exact hEq z hz hzv
  exact h_interpolation A T (clearedAuxiliarySum L v c l₀ l₂ l₃ M) G
    (fun z => σ z ^ (15 * M)) hG hf (fun x _ => (hσ x trivial).pow _) hlocal hjets
    r R (clearedAuxiliaryBound L v c D M R B) hr hR hrad
    (fun z hz => hbound R B hB hbasic z (by
      simpa only [mem_sphere, dist_zero_right] using le_of_eq hz))


open scoped Polynomial
open WeierstrassEllipticZeta


-- Retained proved helper calculations: from_cleared_entire_data
set_option maxHeartbeats 800000
open MvPolynomial
open scoped Polynomial

private def p2m_mc_8_flatten : ℤ[X][X] →+* MvPolynomial (Fin 2) ℤ :=
  Polynomial.eval₂RingHom (Polynomial.eval₂RingHom C (X 0)) (X 1)

private lemma p2m_mc_8_flatten_eval (p : ℤ[X][X]) (θ ν : ℂ) :
    eval₂ (Int.castRingHom ℂ) ![θ, ν] (p2m_mc_8_flatten p) =
      p.eval₂ (Polynomial.aeval θ).toRingHom ν := by
  have h : (eval₂Hom (Int.castRingHom ℂ) ![θ, ν]).comp p2m_mc_8_flatten =
      Polynomial.eval₂RingHom (Polynomial.aeval θ).toRingHom ν := by
    apply Polynomial.ringHom_ext
    · intro q
      have hq : (eval₂Hom (Int.castRingHom ℂ) ![θ, ν]).comp
          (Polynomial.eval₂RingHom C (X 0)) = (Polynomial.aeval θ).toRingHom := by
        apply Polynomial.ringHom_ext <;> simp
      simpa [p2m_mc_8_flatten] using congrArg (fun f : ℤ[X] →+* ℂ => f q) hq
    · simp [p2m_mc_8_flatten]
  exact congrArg (fun f : ℤ[X][X] →+* ℂ => f p) h

private theorem p2m_mc_8_period_arithmetic_jet_systems (L : PeriodPair) (ω z θ ν : ℂ)
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
  let s : Fin 7 → MvPolynomial (Fin 2) ℤ := fun i => p2m_mc_8_flatten (p i)
  let q : MvPolynomial (Fin 2) ℤ := p2m_mc_8_flatten (Polynomial.C d)
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
        simpa [q] using p2m_mc_8_flatten_eval (Polynomial.C d) θ ν
      have hseval (j : Fin 7) : (eval₂Hom (Int.castRingHom ℂ) ![θ, ν]) (s j) =
          (eval₂Hom (Int.castRingHom ℂ) ![θ, ν]) q * periodJetCoordinates L ω z j := by
        change eval₂ _ _ (p2m_mc_8_flatten (p j)) = _
        rw [p2m_mc_8_flatten_eval, hp, show (eval₂Hom (Int.castRingHom ℂ) ![θ, ν]) q = _ from hqeval]
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


open WeierstrassEllipticZeta


-- Retained proved helper calculations: from_period_jet_systems
open Filter


private theorem p2m_mc_9_auxiliary_grid_parameter_data (L : PeriodPair) (ω u₁ u₂ : ℂ)
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


open WeierstrassEllipticZeta
open scoped Polynomial


-- Retained proved helper calculations: from_grid_parameters
open Filter Metric Set
open scoped Topology


private theorem p2m_mc_10_auxiliary_grid_decay_data (L : PeriodPair) (ω u₁ u₂ : ℂ)
    (h_grid : RegularAuxiliaryGridData L ω u₁ u₂)
    (h_parameters : AuxiliaryGridParameterData L ω u₁ u₂) :
    AuxiliaryGridDecayData ω u₁ u₂ := by
  intro B K hB hK
  have hn := tendsto_natCast_atTop_atTop (R := ℝ)
  have hscale := (tendsto_rpow_atTop (by norm_num : 0 < (1 / 72 : ℝ))).comp hn
  have hdecay := TranscendenceTheory.finite_zeros_exponential_derivative_bound
    (1 / 512) (1 / 72) B K (by norm_num) (by norm_num) hB hK
  filter_upwards [h_parameters 1 (by norm_num), hdecay,
    hn.eventually (eventually_ge_atTop (2 : ℝ)), hscale.eventually_ge_atTop 2]
    with N hN hdecay hN2 hscale
  rcases hN with ⟨hm, hl, hs, hq, hsq, hgap, hcount, hupper,
    hmlog, hls, hR, hr, hlarge, hratio, hgrowth⟩
  dsimp only
  let r : ℝ := 4 * auxiliaryS3 N * (‖u₁‖ + ‖u₂‖ + ‖ω‖ + 1)
  let Γ := shiftedAuxiliaryGrid u₁ u₂ ω ![auxiliaryS N, auxiliaryS N, auxiliaryS3 N]
  change 0 < r at hr
  change 2 * r / auxiliaryRadius N ≤ (N : ℝ) ^ (-1 / 36 : ℝ) at hratio
  have hN0 : (0 : ℝ) < N := by linarith only [hN2]
  have hlog : 0 < Real.log N := Real.log_pos (by linarith only [hN2])
  have hR0 : 0 < auxiliaryRadius N := by linarith only [hR]
  have hscale' : 2 * (N : ℝ) ^ (-1 / 36 : ℝ) ≤ (N : ℝ) ^ (-1 / 72 : ℝ) := by
    calc
      _ ≤ (N : ℝ) ^ (1 / 72 : ℝ) * (N : ℝ) ^ (-1 / 36 : ℝ) :=
        mul_le_mul_of_nonneg_right hscale (by positivity)
      _ = _ := by rw [← Real.rpow_add hN0]; norm_num
  have hratio' : 2 * (2 * r) / auxiliaryRadius N ≤ (N : ℝ) ^ (-(1 / 72 : ℝ)) := by
    calc
      _ = 2 * (2 * r / auxiliaryRadius N) := by ring
      _ ≤ 2 * (N : ℝ) ^ (-1 / 36 : ℝ) := mul_le_mul_of_nonneg_left hratio (by norm_num)
      _ ≤ _ := by simpa only [neg_div] using hscale'
  have hrR : 2 * r < auxiliaryRadius N := by
    have hlt := Real.rpow_lt_one_of_one_lt_of_neg
      (by linarith only [hN2] : (1 : ℝ) < N) (by norm_num : -(1 / 72 : ℝ) < 0)
    have h := (div_lt_one hR0).mp (hratio'.trans_lt hlt)
    linarith only [h, hr]
  have hnodes : ∀ z ∈ Γ, ‖z‖ ≤ r := by
    intro z hz
    have hzbound := h_grid.shifted_grid_radius _ z hz
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons] at hzbound
    have hsq' : (auxiliaryS N : ℝ) ≤ auxiliaryS3 N := by exact_mod_cast hsq
    have hq' : (1 : ℝ) ≤ auxiliaryS3 N := by exact_mod_cast hq
    have hu1 := mul_le_mul_of_nonneg_right hsq' (norm_nonneg u₁)
    have hu2 := mul_le_mul_of_nonneg_right hsq' (norm_nonneg u₂)
    have hu3 := mul_le_mul_of_nonneg_right hq' (norm_nonneg u₁)
    dsimp only [r]
    nlinarith only [hzbound, hu1, hu2, hu3, hq',
      mul_nonneg (Nat.cast_nonneg (auxiliaryS3 N)) (norm_nonneg u₁),
      mul_nonneg (Nat.cast_nonneg (auxiliaryS3 N)) (norm_nonneg u₂),
      mul_nonneg (Nat.cast_nonneg (auxiliaryS3 N)) (norm_nonneg ω)]
  intro v hv f G ψ hG hf hψ hGf hjet houter w hw n hn_bound
  have hzero : ∀ x ∈ Γ.image (fun z => z - v),
      ∀ j < auxiliaryL0 N + 1, iteratedDeriv j G x = 0 := by
    intro x hx
    apply (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (hG x trivial)).1
    have hfT := (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (hf x hx)).2
      (hjet x hx)
    rw [analyticOrderAt_congr (hGf x hx)]
    change (auxiliaryL0 N + 1 : ℕ∞) ≤ analyticOrderAt (ψ * f) x
    rw [analyticOrderAt_mul (hψ x hx) (hf x hx)]
    exact hfT.trans le_add_self
  have hcard : (Γ.image (fun z => z - v)).card = Γ.card :=
    Finset.card_image_of_injective _ (by intro a b h; exact sub_left_inj.mp h)
  have hsum : (∑ x ∈ Γ.image (fun z => z - v), (auxiliaryL0 N + 1)) =
      Γ.card * (auxiliaryL0 N + 1) := by
    simp only [Finset.sum_const, nsmul_eq_mul, hcard, Nat.cast_id]
  have hcount' : (1 / 512 : ℝ) * (N : ℝ) ^ 2 ≤
      (∑ x ∈ Γ.image (fun z => z - v), (auxiliaryL0 N + 1) : ℕ) := by
    rw [hsum]
    simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, mul_comm, div_eq_mul_inv,
      one_mul] using hcount
  have hnodes' : ∀ z ∈ Γ.image (fun x => x - v), ‖z‖ ≤ 2 * r := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨x, hx, rfl⟩
    calc
      ‖x - v‖ ≤ ‖x‖ + ‖v‖ := norm_sub_le _ _
      _ ≤ r + r := add_le_add (hnodes x hx) hv
      _ = 2 * r := by ring
  have hn' : (n : ℝ) ≤ K * ((N : ℝ) / Real.log N) := by
    apply hn_bound.trans
    exact mul_le_mul_of_nonneg_left (Nat.floor_le (by positivity)) hK.le
  have hsmall := hdecay G hG (Γ.image (fun z => z - v))
    (fun _ => auxiliaryL0 N + 1) hzero (2 * r) (auxiliaryRadius N)
    (by positivity) hrR hnodes' hcount' hratio' houter w hw n hn'
  have hexponent : -((1 / 512 : ℝ) * (1 / 72) / 2) * (N : ℝ) ^ 2 * Real.log N =
      -(N : ℝ) ^ 2 * Real.log N / 73728 := by ring
  rw [hexponent] at hsmall
  exact ⟨hsmall.1, hsmall.2 f ψ⟩


open WeierstrassEllipticZeta
open scoped Polynomial


-- Retained proved helper calculations: from_entire_sigma_growth
open scoped Polynomial
open Filter

open WeierstrassEllipticZeta


private lemma p2m_mc_15_period_coefficient_of_grid (L : PeriodPair) (ω u₁ u₂ : ℂ)
    (h_grid : RegularAuxiliaryGridData L ω u₁ u₂) (A : Fin 3 → ℕ)
    (v : ℂ) (hv : v ∈ auxiliaryGrid u₁ u₂ ω A) (hvL : v ∈ L.lattice) :
    ∃ a : ℤ, a.natAbs ≤ A 2 ∧ v = a * ω := by
  classical
  obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hv
  let m : Fin 3 → ℤ := fun i => (t i : ℕ)
  have hm := (h_grid.lattice_iff m).mp hvL
  refine ⟨m 2, ?_, ?_⟩
  · simp [m, Nat.le_of_lt (t 2).isLt]
  · change integerGridPoint u₁ u₂ ω m = _
    simp [integerGridPoint, hm.1, hm.2]

/-- The two actual sigma regularizers have uniformly controlled reciprocal norms. -/
private theorem p2m_mc_15_sigma_auxiliary_regularizer_inverse_bounds_from_progressions
    (L : PeriodPair) (ω u₁ u₂ : ℂ)
    (h_grid : RegularAuxiliaryGridData L ω u₁ u₂)
    (h_parameters : AuxiliaryGridParameterData L ω u₁ u₂)
    (D : EllipticSigmaDifferentialData L)
    (hne : ∀ z : ℂ, z ∉ L.lattice → D.sigma z ≠ 0)
    (hinv : ∀ u ω : ℂ, u ∉ L.lattice → ω ∈ L.lattice →
      ∃ C : ℝ, 0 < C ∧ ∀ (n : ℤ) (k : ℕ),
        ‖D.sigma (u + n * ω) ^ k‖⁻¹ ≤
          Real.exp (C * k * (1 + (n : ℝ) ^ 2))) :
    (∀ z : ℂ, z ∉ L.lattice → D.sigma z ≠ 0) ∧
      ∀ᶠ N : ℕ in atTop,
        ‖D.sigma (u₁ / 2) ^ (15 * auxiliaryL N)‖⁻¹ ≤ Real.exp ((N : ℝ) ^ 2) ∧
        ∀ v ∈ auxiliaryGrid u₁ u₂ ω
            ![3 * auxiliaryS N, 3 * auxiliaryS N, 3 * auxiliaryS3 N],
          v ∈ L.lattice →
            ‖D.sigma (u₁ / 2 + v) ^ (3 * auxiliaryL N)‖⁻¹ ≤
              Real.exp ((N : ℝ) ^ 2) := by
  refine ⟨hne, ?_⟩
  have hu : u₁ / 2 ∉ L.lattice := by
    simpa [integerGridPoint] using h_grid.shifted_regular (fun _ => 0)
  have hω : ω ∈ L.lattice := by
    simpa [integerGridPoint] using (h_grid.lattice_iff ![0, 0, 1]).mpr (by simp)
  obtain ⟨C, hC, hbound⟩ := hinv (u₁ / 2) ω hu hω
  filter_upwards [h_parameters (30 * C) (by positivity), eventually_ge_atTop (1 : ℕ)] with N hpar hN
  let l := auxiliaryL N
  let q := auxiliaryS3 N
  let R := auxiliaryRadius N
  let U := ‖u₁‖ + ‖u₂‖ + ‖ω‖ + 1
  let r := 4 * (q : ℝ) * U
  rcases hpar with ⟨_, _, _, _, _, _, _, _, _, _, hR, _, _, hratio, hgrowth⟩
  have hR' : 1 ≤ R := hR
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR'
  have hU : 1 ≤ U := by
    dsimp [U]
    nlinarith [norm_nonneg u₁, norm_nonneg u₂, norm_nonneg ω]
  have hratio' : 2 * r / R ≤ 1 := hratio.trans
    (Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hN) (by norm_num))
  have h2r : 2 * r ≤ R := (div_le_one hRpos).mp hratio'
  have hqR : (q : ℝ) ≤ R := by
    have h := mul_le_mul_of_nonneg_left hU (show 0 ≤ (q : ℝ) by positivity)
    dsimp only [r] at h2r
    nlinarith [show 0 ≤ (q : ℝ) by positivity]
  have hRR : 1 ≤ R ^ 2 := by nlinarith
  have hgrowth' : 30 * C * (l : ℝ) * R ^ 2 ≤ (N : ℝ) ^ 2 := hgrowth
  constructor
  · have h := hbound 0 (15 * l)
    simp only [Int.cast_zero, zero_mul, add_zero, zero_pow (by norm_num : 2 ≠ 0),
      Nat.cast_mul, Nat.cast_ofNat, mul_one] at h
    apply h.trans (Real.exp_le_exp.mpr ?_)
    have hm := mul_le_mul_of_nonneg_left hRR
      (show 0 ≤ 15 * C * (l : ℝ) by positivity)
    nlinarith [show 0 ≤ C * (l : ℝ) * R ^ 2 by positivity]
  · intro v hv hvL
    obtain ⟨a, ha, rfl⟩ := p2m_mc_15_period_coefficient_of_grid L ω u₁ u₂ h_grid _ v hv hvL
    have ha' : (a.natAbs : ℝ) ≤ 3 * q := by
      change a.natAbs ≤ 3 * auxiliaryS3 N at ha
      exact_mod_cast ha
    have habs : |(a : ℝ)| ≤ 3 * R := by
      have hh : (a.natAbs : ℝ) ≤ 3 * R := ha'.trans (by linarith)
      simpa using hh
    have hasq : (a : ℝ) ^ 2 ≤ 9 * R ^ 2 := by
      have hh := mul_self_le_mul_self (abs_nonneg (a : ℝ)) habs
      nlinarith [sq_abs (a : ℝ)]
    have hb : 1 + (a : ℝ) ^ 2 ≤ 10 * R ^ 2 := by nlinarith
    apply (hbound a (3 * l)).trans (Real.exp_le_exp.mpr ?_)
    have hh := mul_le_mul_of_nonneg_left hb (show 0 ≤ 3 * C * (l : ℝ) by positivity)
    push_cast
    nlinarith


-- Retained proved helper calculations: from_sigma_inverse_bounds
open scoped Polynomial
open Filter

open WeierstrassEllipticZeta

set_option maxHeartbeats 800000

/-- The period denominator is absorbed while retaining quadratic logarithmic decay. -/
private theorem p2m_mc_16_period_auxiliary_arithmetic_decay_from_first_derivative
    (L : PeriodPair) (ω u₁ u₂ : ℂ)
    (h_parameters : AuxiliaryGridParameterData L ω u₁ u₂)
    (D : EllipticSigmaDifferentialData L) (δ : ℂ)
    (h_sigma_inverse : ∀ᶠ N : ℕ in Filter.atTop,
      ‖D.sigma (u₁ / 2) ^ (15 * auxiliaryL N)‖⁻¹ ≤ Real.exp ((N : ℝ) ^ 2) ∧
      ∀ v ∈ auxiliaryGrid u₁ u₂ ω
          ![3 * auxiliaryS N, 3 * auxiliaryS N, 3 * auxiliaryS3 N],
        v ∈ L.lattice →
          ‖D.sigma (u₁ / 2 + v) ^ (3 * auxiliaryL N)‖⁻¹ ≤
            Real.exp ((N : ℝ) ^ 2))
    (h_first : ∀ B K : ℝ, 0 ≤ B → 0 < K → ∀ᶠ N : ℕ in atTop,
      let m := auxiliaryL0 N
      let l := auxiliaryL N
      let r := 4 * (auxiliaryS3 N : ℝ) * (‖u₁‖ + ‖u₂‖ + ‖ω‖ + 1)
      ∀ c : Fin (m + 1) × Fin (l + 1) × Fin (l + 1) → ℂ,
        (∑ i, ‖c i‖) ≤ Real.exp (B * N) →
        let f : ℂ → ℂ := fun z => ∑ i, c i * z ^ i.1.val *
          L.weierstrassP z ^ i.2.1.val * weierstrassZeta L z ^ i.2.2.val
        (∀ x ∈ shiftedAuxiliaryGrid u₁ u₂ ω
            ![auxiliaryS N, auxiliaryS N, auxiliaryS3 N],
          ∀ j < m + 1, iteratedDeriv j f x = 0) →
        ∀ w : ℂ, w ∉ L.lattice → ‖w‖ + 1 ≤ 2 * r →
          ‖D.sigma w ^ (3 * l)‖⁻¹ ≤ Real.exp ((N : ℝ) ^ 2) →
          ∀ n : ℕ, (n : ℝ) ≤ K * m →
            (∀ j < n, iteratedDeriv j f w = 0) →
            ‖iteratedDeriv n f w‖ ≤
              Real.exp (-(N : ℝ) ^ 2 * Real.log N / 73728)) :
    ∀ B K : ℝ, 0 ≤ B → 0 < K → ∀ᶠ N : ℕ in atTop,
      let m := auxiliaryL0 N
      let l := auxiliaryL N
      ∀ c : Fin (m + 1) × Fin (l + 1) × Fin (l + 1) → ℂ,
        (∀ i, ‖c i‖ ≤ Real.exp (B * N)) →
        let f : ℂ → ℂ := fun z => ∑ i, c i * z ^ i.1.val *
          L.weierstrassP z ^ i.2.1.val * weierstrassZeta L z ^ i.2.2.val
        (∀ x ∈ shiftedAuxiliaryGrid u₁ u₂ ω
            ![auxiliaryS N, auxiliaryS N, auxiliaryS3 N],
          ∀ j < m + 1, iteratedDeriv j f x = 0) →
        ∀ v ∈ auxiliaryGrid u₁ u₂ ω
            ![3 * auxiliaryS N, 3 * auxiliaryS N, 3 * auxiliaryS3 N],
          v ∈ L.lattice → ∀ n : ℕ, (n : ℝ) ≤ K * m →
            (∀ j < n, iteratedDeriv j f (u₁ / 2 + v) = 0) →
            ‖δ ^ (7 * (m + 2 * l + n)) * iteratedDeriv n f (u₁ / 2 + v)‖ ≤
              Real.exp (-(N : ℝ) ^ 2 * Real.log N / 147456) := by
  intro B K hB hK
  let C := 7 * (‖δ‖ + 1) * (K + 3)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hlog : ∀ᶠ N : ℕ in atTop, max 1 (147456 * C) ≤ Real.log N :=
    (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))).eventually
      (eventually_ge_atTop _)
  filter_upwards [h_parameters 1 zero_lt_one, h_sigma_inverse,
    h_first (B + 3) K (by positivity) hK, hlog, eventually_ge_atTop (1 : ℕ)]
    with N hpar hinv hfirst hlog hN
  let m := auxiliaryL0 N
  let l := auxiliaryL N
  rcases hpar with ⟨_, _, hs, _, _, _, _, _, hmlog, hls, _, hr, hgeom, _, _⟩
  have hlog1 : 1 ≤ Real.log N := (le_max_left _ _).trans hlog
  have hlogC : 147456 * C ≤ Real.log N := (le_max_right _ _).trans hlog
  have hmN : (m : ℝ) ≤ N := by
    change (m : ℝ) * Real.log N ≤ N at hmlog
    nlinarith [mul_le_mul_of_nonneg_left hlog1 (Nat.cast_nonneg m)]
  have hlm : l ≤ m := by
    change l * auxiliaryS N ^ 2 ≤ m at hls
    have hs2 : 1 ≤ auxiliaryS N ^ 2 := by nlinarith
    nlinarith
  have hlN : (l : ℝ) ≤ N := (Nat.cast_le.mpr hlm).trans hmN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNN : (N : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith
  have hmexp : (m : ℝ) + 1 ≤ Real.exp N := by
    linarith [Real.add_one_le_exp (N : ℝ)]
  have hlexp : (l : ℝ) + 1 ≤ Real.exp N := by
    linarith [Real.add_one_le_exp (N : ℝ)]
  dsimp only
  intro c hc
  let f : ℂ → ℂ := fun z => ∑ i, c i * z ^ i.1.val *
    L.weierstrassP z ^ i.2.1.val * weierstrassZeta L z ^ i.2.2.val
  have hcard : ((m + 1 : ℝ) * (l + 1) * (l + 1)) ≤ Real.exp (3 * N) := by
    calc
      _ ≤ Real.exp N * Real.exp N * Real.exp N := by
        exact mul_le_mul (mul_le_mul hmexp hlexp (by positivity) (by positivity))
          hlexp (by positivity) (by positivity)
      _ = _ := by rw [show 3 * (N : ℝ) = N + N + N by ring, Real.exp_add, Real.exp_add]
  have hsum : (∑ i, ‖c i‖) ≤ Real.exp ((B + 3) * N) := by
    calc
      _ ≤ ∑ _i : Fin (m + 1) × Fin (l + 1) × Fin (l + 1), Real.exp (B * N) :=
        Finset.sum_le_sum (fun i _ => hc i)
      _ = ((m + 1 : ℝ) * (l + 1) * (l + 1)) * Real.exp (B * N) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod,
          Fintype.card_fin, nsmul_eq_mul, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
        ring
      _ ≤ Real.exp (3 * N) * Real.exp (B * N) :=
        mul_le_mul_of_nonneg_right hcard (Real.exp_pos _).le
      _ = _ := by rw [show (B + 3) * (N : ℝ) = 3 * N + B * N by ring, Real.exp_add]
  intro hzero v hv hvL n hn hbefore
  have hv' : u₁ / 2 + v ∈ shiftedAuxiliaryGrid u₁ u₂ ω
      ![3 * auxiliaryS N, 3 * auxiliaryS N, 3 * auxiliaryS3 N] := by
    exact Finset.mem_image.mpr ⟨v, hv, add_comm _ _⟩
  obtain ⟨hwL, hwR⟩ := hgeom _ hv'
  have hsmall := hfirst c hsum hzero (u₁ / 2 + v) hwL
    (by linarith) (hinv.2 v hv hvL) n hn hbefore
  have hpower : ‖δ ^ (7 * (m + 2 * l + n))‖ ≤ Real.exp (C * (N : ℝ) ^ 2) := by
    rw [norm_pow]
    have hdexp : ‖δ‖ ≤ Real.exp ‖δ‖ := by linarith [Real.add_one_le_exp ‖δ‖]
    calc
      _ ≤ (Real.exp ‖δ‖) ^ (7 * (m + 2 * l + n)) :=
        pow_le_pow_left₀ (norm_nonneg δ) hdexp _
      _ = Real.exp ((7 * (m + 2 * l + n) : ℕ) * ‖δ‖) := (Real.exp_nat_mul _ _).symm
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        have hnN : (n : ℝ) ≤ K * N := hn.trans (mul_le_mul_of_nonneg_left hmN hK.le)
        have hp : (7 * (m + 2 * l + n) : ℝ) ≤ 7 * (3 + K) * N := by
          nlinarith
        push_cast
        calc
          _ ≤ (7 * (3 + K) * N) * ‖δ‖ := mul_le_mul_of_nonneg_right hp (norm_nonneg δ)
          _ ≤ C * N := by dsimp [C]; nlinarith [norm_nonneg δ]
          _ ≤ _ := mul_le_mul_of_nonneg_left hNN hC
  calc
    _ = ‖δ ^ (7 * (m + 2 * l + n))‖ * ‖iteratedDeriv n f (u₁ / 2 + v)‖ := norm_mul _ _
    _ ≤ Real.exp (C * (N : ℝ) ^ 2) *
        Real.exp (-(N : ℝ) ^ 2 * Real.log N / 73728) :=
      mul_le_mul hpower hsmall (norm_nonneg _) (Real.exp_pos _).le
    _ = Real.exp (C * (N : ℝ) ^ 2 - (N : ℝ) ^ 2 * Real.log N / 73728) := by
      rw [sub_eq_add_neg, Real.exp_add]
      congr 2
      ring
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_right hlogC (sq_nonneg (N : ℝ))]


-- Retained proved helper calculations: from_period_jet_decay
open scoped Polynomial
open Filter

open WeierstrassEllipticZeta

open Set
set_option maxHeartbeats 800000

open Filter Metric

private lemma p2m_mc_17_weighted_auxiliary_radius_bound (N m : ℕ) (hN : (1 : ℝ) ≤ N)
    (hm : (m : ℝ) * Real.log N ≤ N) :
    auxiliaryRadius N ^ m ≤ Real.exp N := by
  have hN0 : (0 : ℝ) < N := lt_of_lt_of_le zero_lt_one hN
  rw [auxiliaryRadius, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le,
    Real.rpow_def_of_pos hN0]
  have hlog : 0 ≤ Real.log N := Real.log_nonneg hN
  apply Real.exp_le_exp.mpr
  nlinarith [mul_nonneg (Nat.cast_nonneg m) hlog]

private lemma p2m_mc_17_nonnegative_power_exp_bound (x : ℝ) (hx : 0 ≤ x) (n : ℕ) :
    x ^ n ≤ Real.exp ((n : ℝ) * x) := by
  rw [Real.exp_nat_mul]
  apply pow_le_pow_left₀ hx
  linarith [Real.add_one_le_exp x]

/-- Common moving-coordinate denominators preserve an exponential quadratic envelope. -/
private theorem p2m_mc_17_scaled_cleared_auxiliary_outer_bound
    (L : PeriodPair) (ω u₁ u₂ : ℂ)
    (h_parameters : AuxiliaryGridParameterData L ω u₁ u₂)
    (σ : ℂ → ℂ) (S : Fin 3 → ℂ → ℂ)
    (A : ℝ) (hA : 0 < A)
    (h_sigma_growth : ∀ z : ℂ, ‖σ z‖ ≤ Real.exp (A * (1 + ‖z‖ ^ 2)))
    (h_factor_growth : ∀ (z : ℂ) (j : Fin 3),
      ‖S j z‖ ≤ Real.exp (A * (1 + ‖z‖ ^ 2)))
    (h_weighted : ∀ {ι : Type} [Fintype ι] (v : ℂ), v ∉ L.lattice → ∀
    (c : ι → ℂ) (l₀ l₂ l₃ : ι → ℕ) (D M : ℕ)
    , (∀ i, l₀ i ≤ D) → (∀ i, l₂ i ≤ M) → (∀ i, l₃ i ≤ M) →
    ∃ G : ℂ → ℂ, AnalyticOnNhd ℂ G univ ∧
      (∀ z : ℂ, z ∉ L.lattice → z + v ∉ L.lattice →
        G z = σ z ^ (15 * M) * ∑ i, c i *
          clearedAdditionMonomial L v M (l₀ i) (l₂ i) (l₃ i) z) ∧
      ∀ R B : ℝ, 1 ≤ B →
        (∀ z : ℂ, ‖z‖ ≤ R → ‖σ z‖ ≤ B ∧ ∀ j, ‖S j z‖ ≤ B) →
        ∀ z : ℂ, ‖z‖ ≤ R →
          ‖G z‖ ≤ (∑ i, ‖c i‖) * (max 1 (R + ‖v‖)) ^ D *
            (36 : ℝ) ^ (3 * M) *
            (1 + ‖weierstrassZeta L v‖ + ‖L.weierstrassP v‖ +
              ‖L.derivWeierstrassP v‖) ^ (5 * M) * B ^ (15 * M)) :
    ∀ B : ℝ, 0 ≤ B → ∀ᶠ N : ℕ in Filter.atTop,
      let m := auxiliaryL0 N
      let l := auxiliaryL N
      let s := auxiliaryS N
      let R := auxiliaryRadius N
      ∀ c : Fin (m + 1) × Fin (l + 1) × Fin (l + 1) → ℂ,
        (∑ i, ‖c i‖) ≤ Real.exp (B * N) →
        ∀ v : ℂ, ‖v‖ ≤ R → v ∉ L.lattice → ∀ Q : ℂ,
          ‖Q‖ + ‖Q * weierstrassZeta L v‖ + ‖Q * L.weierstrassP v‖ +
              ‖Q * L.derivWeierstrassP v‖ ≤ Real.exp (B * ((s : ℝ) ^ 2 + Real.log N)) →
          ∃ G : ℂ → ℂ, AnalyticOnNhd ℂ G Set.univ ∧
            (∀ z : ℂ, z ∉ L.lattice → z + v ∉ L.lattice →
              G z = σ z ^ (15 * l) * (Q ^ (5 * l) *
                clearedAuxiliarySum L v c (fun i => i.1.val) (fun i => i.2.1.val)
                  (fun i => i.2.2.val) l z)) ∧
            ∀ z : ℂ, ‖z‖ ≤ R → ‖G z‖ ≤ Real.exp ((11 * B + 112) * (N : ℝ) ^ 2) := by
  intro B hB
  have hlog : ∀ᶠ N : ℕ in atTop, 1 ≤ Real.log N :=
    (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))).eventually
      (eventually_ge_atTop _)
  filter_upwards [h_parameters (30 * A) (by positivity), hlog,
    eventually_ge_atTop (1 : ℕ)] with N hpar hlog hN
  let m := auxiliaryL0 N
  let l := auxiliaryL N
  let s := auxiliaryS N
  let R := auxiliaryRadius N
  rcases hpar with ⟨_, _, hs, _, _, _, _, _, hmlog, hls, hR, _, _, _, hAG⟩
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNN : (N : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith
  have hmN : (m : ℝ) ≤ N := by
    change (m : ℝ) * Real.log N ≤ N at hmlog
    nlinarith [mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg m)]
  have hlm : l ≤ m := by
    change l * s ^ 2 ≤ m at hls
    change 2 ≤ s at hs
    have hs2 : 1 ≤ s ^ 2 := by nlinarith
    nlinarith
  have hlN : (l : ℝ) ≤ N := (Nat.cast_le.mpr hlm).trans hmN
  have hllog : (l : ℝ) * Real.log N ≤ N :=
    (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hlm) (by linarith)).trans hmlog
  have hlsR : (l : ℝ) * (s : ℝ) ^ 2 ≤ m := by exact_mod_cast hls
  have hR1 : 1 ≤ R := hR
  have hRR : 1 ≤ R ^ 2 := by nlinarith
  have hRpow := p2m_mc_17_weighted_auxiliary_radius_bound N m hN1 hmlog
  have htwo : (2 : ℝ) ^ m ≤ Real.exp (2 * N) := by
    apply (p2m_mc_17_nonnegative_power_exp_bound 2 (by norm_num) m).trans
    apply Real.exp_le_exp.mpr
    nlinarith
  have hconst : (36 : ℝ) ^ (3 * l) ≤ Real.exp (108 * N) := by
    apply (p2m_mc_17_nonnegative_power_exp_bound 36 (by norm_num) (3 * l)).trans
    apply Real.exp_le_exp.mpr
    push_cast
    nlinarith
  let H := Real.exp (A * (1 + R ^ 2))
  have hH : 1 ≤ H := Real.one_le_exp (by positivity)
  have hbasic (z : ℂ) (hz : ‖z‖ ≤ R) :
      ‖σ z‖ ≤ H ∧ ∀ j, ‖S j z‖ ≤ H := by
    have hzz : ‖z‖ ^ 2 ≤ R ^ 2 := by nlinarith [norm_nonneg z]
    have hh : Real.exp (A * (1 + ‖z‖ ^ 2)) ≤ H := by
      apply Real.exp_le_exp.mpr
      nlinarith
    exact ⟨(h_sigma_growth z).trans hh, fun j => (h_factor_growth z j).trans hh⟩
  have hHp : H ^ (15 * l) ≤ Real.exp ((N : ℝ) ^ 2) := by
    dsimp [H]
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    push_cast
    change 30 * A * (l : ℝ) * R ^ 2 ≤ (N : ℝ) ^ 2 at hAG
    nlinarith [mul_le_mul_of_nonneg_left hRR (show 0 ≤ 15 * A * (l : ℝ) by positivity)]
  dsimp only
  intro c hc v hvR hv Q hQ
  obtain ⟨G, hG, hGeq, hGbound⟩ := h_weighted v hv c (fun i => i.1.val)
    (fun i => i.2.1.val) (fun i => i.2.2.val) m l
    (fun i => by have := i.1.isLt; omega)
    (fun i => by have := i.2.1.isLt; omega)
    (fun i => by have := i.2.2.isLt; omega)
  let V := 1 + ‖weierstrassZeta L v‖ + ‖L.weierstrassP v‖ + ‖L.derivWeierstrassP v‖
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hQV : ‖Q‖ * V ≤ Real.exp (B * ((s : ℝ) ^ 2 + Real.log N)) := by
    calc
      _ = ‖Q‖ + ‖Q * weierstrassZeta L v‖ + ‖Q * L.weierstrassP v‖ +
          ‖Q * L.derivWeierstrassP v‖ := by simp only [norm_mul]; dsimp [V]; ring
      _ ≤ _ := hQ
  have hmoving : ‖Q‖ ^ (5 * l) * V ^ (5 * l) ≤ Real.exp (10 * B * N) := by
    rw [← mul_pow]
    apply (pow_le_pow_left₀ (mul_nonneg (norm_nonneg Q) hV) hQV (5 * l)).trans
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    push_cast
    have hsuml : (l : ℝ) * ((s : ℝ) ^ 2 + Real.log N) ≤ 2 * N := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hsuml (show 0 ≤ 5 * B by positivity)]
  have hXpow : (max 1 (R + ‖v‖)) ^ m ≤ Real.exp (3 * N) := by
    have hX : max 1 (R + ‖v‖) ≤ 2 * R := max_le (by linarith) (by linarith)
    calc
      _ ≤ (2 * R) ^ m := pow_le_pow_left₀ (by positivity) hX m
      _ = (2 : ℝ) ^ m * R ^ m := mul_pow _ _ _
      _ ≤ Real.exp (2 * N) * Real.exp N :=
        mul_le_mul htwo hRpow (by positivity) (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  refine ⟨fun z => Q ^ (5 * l) * G z, ?_, ?_, ?_⟩
  · intro z _
    exact analyticAt_const.mul (hG z trivial)
  · intro z hz hzv
    dsimp only
    rw [hGeq z hz hzv]
    dsimp [clearedAuxiliarySum]
    ring
  · intro z hz
    have hg := hGbound R H hH hbasic z hz
    change ‖G z‖ ≤ (∑ i, ‖c i‖) * (max 1 (R + ‖v‖)) ^ m *
      (36 : ℝ) ^ (3 * l) * V ^ (5 * l) * H ^ (15 * l) at hg
    calc
      _ = ‖Q‖ ^ (5 * l) * ‖G z‖ := by rw [norm_mul, norm_pow]
      _ ≤ ‖Q‖ ^ (5 * l) * ((∑ i, ‖c i‖) * (max 1 (R + ‖v‖)) ^ m *
          (36 : ℝ) ^ (3 * l) * V ^ (5 * l) * H ^ (15 * l)) :=
        mul_le_mul_of_nonneg_left hg (by positivity)
      _ = (∑ i, ‖c i‖) * (max 1 (R + ‖v‖)) ^ m * (36 : ℝ) ^ (3 * l) *
          (‖Q‖ ^ (5 * l) * V ^ (5 * l)) * H ^ (15 * l) := by ring
      _ ≤ Real.exp (B * N) * Real.exp (3 * N) * Real.exp (108 * N) *
          Real.exp (10 * B * N) * Real.exp ((N : ℝ) ^ 2) := by gcongr
      _ = Real.exp ((11 * B + 111) * N + (N : ℝ) ^ 2) := by
        rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        nlinarith [mul_le_mul_of_nonneg_left hNN (show 0 ≤ 11 * B + 111 by positivity)]


-- Retained proved helper calculations: from_scaled_cleared_growth
open scoped Polynomial
open Filter

open WeierstrassEllipticZeta

open Metric Set
open scoped Topology
set_option maxHeartbeats 800000

private lemma p2m_mc_18_translated_shifted_grid_regular
    (L : PeriodPair) (ω u₁ u₂ : ℂ) (h_grid : RegularAuxiliaryGridData L ω u₁ u₂)
    (A B : Fin 3 → ℕ) (x v : ℂ)
    (hx : x ∈ shiftedAuxiliaryGrid u₁ u₂ ω A) (hv : v ∈ auxiliaryGrid u₁ u₂ ω B) :
    x - v ∉ L.lattice := by
  rcases Finset.mem_image.mp hx with ⟨y, hy, rfl⟩
  rcases Finset.mem_image.mp hy with ⟨a, _, rfl⟩
  rcases Finset.mem_image.mp hv with ⟨b, _, rfl⟩
  have heq : integerGridPoint u₁ u₂ ω (fun i => (a i : ℤ)) + u₁ / 2 -
      integerGridPoint u₁ u₂ ω (fun i => (b i : ℤ)) =
      integerGridPoint u₁ u₂ ω (fun i => (a i : ℤ) - (b i : ℤ)) + u₁ / 2 := by
    simp only [integerGridPoint, Int.cast_sub]
    ring
  rw [heq]
  exact h_grid.shifted_regular (fun i => (a i : ℤ) - (b i : ℤ))

private lemma p2m_mc_18_enlarged_grid_radius_bound
    (L : PeriodPair) (ω u₁ u₂ : ℂ) (h_grid : RegularAuxiliaryGridData L ω u₁ u₂)
    (s q : ℕ) (hsq : s ≤ q) (hq : 1 ≤ q) (v : ℂ)
    (hv : v ∈ auxiliaryGrid u₁ u₂ ω ![3 * s, 3 * s, 3 * q]) :
    ‖v‖ ≤ 4 * (q : ℝ) * (‖u₁‖ + ‖u₂‖ + ‖ω‖ + 1) := by
  have hv' : v + u₁ / 2 ∈ shiftedAuxiliaryGrid u₁ u₂ ω ![3 * s, 3 * s, 3 * q] :=
    Finset.mem_image.mpr ⟨v, hv, rfl⟩
  have hrad := h_grid.shifted_grid_radius _ _ hv'
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, Nat.cast_mul, Nat.cast_ofNat] at hrad
  have hnorm : ‖u₁ / 2‖ = ‖u₁‖ / 2 := by norm_num [norm_div]
  have htriangle := norm_sub_le (v + u₁ / 2) (u₁ / 2)
  rw [add_sub_cancel_right, hnorm] at htriangle
  have hsqr : (s : ℝ) ≤ q := by exact_mod_cast hsq
  have hqr : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have h1 := mul_le_mul_of_nonneg_right hsqr (norm_nonneg u₁)
  have h2 := mul_le_mul_of_nonneg_right hsqr (norm_nonneg u₂)
  have h3 := mul_le_mul_of_nonneg_right hqr (norm_nonneg u₁)
  nlinarith only [hrad, htriangle, h1, h2, h3, hqr,
    mul_nonneg (Nat.cast_nonneg q) (norm_nonneg u₁),
    mul_nonneg (Nat.cast_nonneg q) (norm_nonneg u₂),
    mul_nonneg (Nat.cast_nonneg q) (norm_nonneg ω)]

/-- Nonlattice interpolation recovers the exact cleared first derivative at the fixed base point. -/
private theorem p2m_mc_18_scaled_nonlattice_first_derivative_decay
    (L : PeriodPair) (ω u₁ u₂ : ℂ)
    (h_grid : RegularAuxiliaryGridData L ω u₁ u₂)
    (h_parameters : AuxiliaryGridParameterData L ω u₁ u₂)
    (h_decay : AuxiliaryGridDecayData ω u₁ u₂)
    (D : EllipticSigmaDifferentialData L)
    (h_sigma_nonzero : ∀ z : ℂ, z ∉ L.lattice → D.sigma z ≠ 0)
    (h_sigma_inverse : ∀ᶠ N : ℕ in Filter.atTop,
      ‖D.sigma (u₁ / 2) ^ (15 * auxiliaryL N)‖⁻¹ ≤ Real.exp ((N : ℝ) ^ 2))
    (h_scaled_cleared_growth : ∀ B : ℝ, 0 ≤ B → ∀ᶠ N : ℕ in Filter.atTop,
      let m := auxiliaryL0 N
      let l := auxiliaryL N
      let s := auxiliaryS N
      let R := auxiliaryRadius N
      ∀ c : Fin (m + 1) × Fin (l + 1) × Fin (l + 1) → ℂ,
        (∑ i, ‖c i‖) ≤ Real.exp (B * N) →
        ∀ v : ℂ, ‖v‖ ≤ R → v ∉ L.lattice → ∀ Q : ℂ,
          ‖Q‖ + ‖Q * weierstrassZeta L v‖ + ‖Q * L.weierstrassP v‖ +
              ‖Q * L.derivWeierstrassP v‖ ≤ Real.exp (B * ((s : ℝ) ^ 2 + Real.log N)) →
          ∃ G : ℂ → ℂ, AnalyticOnNhd ℂ G Set.univ ∧
            (∀ z : ℂ, z ∉ L.lattice → z + v ∉ L.lattice →
              G z = D.sigma z ^ (15 * l) * (Q ^ (5 * l) *
                clearedAuxiliarySum L v c (fun i => i.1.val) (fun i => i.2.1.val)
                  (fun i => i.2.2.val) l z)) ∧
            ∀ z : ℂ, ‖z‖ ≤ R → ‖G z‖ ≤ Real.exp ((11 * B + 112) * (N : ℝ) ^ 2))
    (h_first : ∀ {ι : Type} [Fintype ι] (v : ℂ), v ∉ L.lattice → ∀
    (c : ι → ℂ) (l₀ l₂ l₃ : ι → ℕ) (M : ℕ)
    (z : ℂ), z ∉ L.lattice → z + v ∉ L.lattice →
    AnalyticAt ℂ (clearedAuxiliarySum L v c l₀ l₂ l₃ M) z ∧
      ∀ n : ℕ,
        (∀ j < n, iteratedDeriv j (fun w => ∑ i, c i * w ^ l₀ i *
          L.weierstrassP w ^ l₂ i * weierstrassZeta L w ^ l₃ i) (z + v) = 0) →
        iteratedDeriv n (clearedAuxiliarySum L v c l₀ l₂ l₃ M) z =
          (2 * (L.weierstrassP v - L.weierstrassP z)) ^ (3 * M) *
            iteratedDeriv n (fun w => ∑ i, c i * w ^ l₀ i *
              L.weierstrassP w ^ l₂ i * weierstrassZeta L w ^ l₃ i) (z + v)) :
    ∀ B K : ℝ, 0 ≤ B → 0 < K → ∀ᶠ N : ℕ in Filter.atTop,
      let m := auxiliaryL0 N
      let l := auxiliaryL N
      let s := auxiliaryS N
      ∀ c : Fin (m + 1) × Fin (l + 1) × Fin (l + 1) → ℂ,
        (∑ i, ‖c i‖) ≤ Real.exp (B * N) →
        let F : ℂ → ℂ := fun w => ∑ i, c i * w ^ i.1.val *
          L.weierstrassP w ^ i.2.1.val * weierstrassZeta L w ^ i.2.2.val
        (∀ x ∈ shiftedAuxiliaryGrid u₁ u₂ ω ![s, s, auxiliaryS3 N],
          ∀ j < m + 1, iteratedDeriv j F x = 0) →
        ∀ v ∈ auxiliaryGrid u₁ u₂ ω ![3 * s, 3 * s, 3 * auxiliaryS3 N],
          v ∉ L.lattice → ∀ Q : ℂ,
            ‖Q‖ + ‖Q * weierstrassZeta L v‖ + ‖Q * L.weierstrassP v‖ +
              ‖Q * L.derivWeierstrassP v‖ ≤ Real.exp (B * ((s : ℝ) ^ 2 + Real.log N)) →
            ∀ n : ℕ, (n : ℝ) ≤ K * m →
              (∀ j < n, iteratedDeriv j F (u₁ / 2 + v) = 0) →
              ‖Q ^ (5 * l) * (2 * (L.weierstrassP v - L.weierstrassP (u₁ / 2))) ^
                (3 * l) * iteratedDeriv n F (u₁ / 2 + v)‖ ≤
                  Real.exp (-(N : ℝ) ^ 2 * Real.log N / 73728) := by
  intro B K hB hK
  filter_upwards [h_parameters 1 zero_lt_one, h_sigma_inverse,
    h_scaled_cleared_growth B hB, h_decay (11 * B + 112) K (by positivity) hK,
    eventually_ge_atTop (1 : ℕ)] with N hpar hinv hgrowth hdec hN
  let m := auxiliaryL0 N
  let l := auxiliaryL N
  let s := auxiliaryS N
  let q := auxiliaryS3 N
  let R := auxiliaryRadius N
  let r := 4 * (q : ℝ) * (‖u₁‖ + ‖u₂‖ + ‖ω‖ + 1)
  let Γ := shiftedAuxiliaryGrid u₁ u₂ ω ![s, s, q]
  rcases hpar with ⟨_, _, _, hq, hsq, _, _, _, _, _, hR, hr, _, hratio, _⟩
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hratio' : 2 * r / R ≤ 1 := hratio.trans
    (Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hN) (by norm_num))
  have h2r : 2 * r ≤ R := (div_le_one hRpos).mp hratio'
  have hbase : u₁ / 2 ∉ L.lattice := by
    simpa [integerGridPoint] using h_grid.shifted_regular (fun _ => 0)
  have hbaseR : ‖u₁ / 2‖ + 1 ≤ 2 * r := by
    have hnorm : ‖u₁ / 2‖ = ‖u₁‖ / 2 := by norm_num [norm_div]
    have hqr : (1 : ℝ) ≤ q := by exact_mod_cast hq
    have hqu := mul_le_mul_of_nonneg_right hqr (norm_nonneg u₁)
    rw [hnorm]
    dsimp only [r]
    nlinarith only [hqr, hqu,
      mul_nonneg (Nat.cast_nonneg q) (norm_nonneg u₁),
      mul_nonneg (Nat.cast_nonneg q) (norm_nonneg u₂),
      mul_nonneg (Nat.cast_nonneg q) (norm_nonneg ω)]
  dsimp only
  intro c hc
  let F : ℂ → ℂ := fun w => ∑ i, c i * w ^ i.1.val *
    L.weierstrassP w ^ i.2.1.val * weierstrassZeta L w ^ i.2.2.val
  intro hzero v hv hvL Q hQ n hn hbefore
  have hvr : ‖v‖ ≤ r := p2m_mc_18_enlarged_grid_radius_bound L ω u₁ u₂ h_grid s q hsq hq v hv
  have hvR : ‖v‖ ≤ R := hvr.trans (by linarith)
  obtain ⟨G, hG, hGeq, hGbound⟩ := hgrowth c hc v hvR hvL Q hQ
  let f : ℂ → ℂ := fun z => Q ^ (5 * l) *
    clearedAuxiliarySum L v c (fun i => i.1.val) (fun i => i.2.1.val)
      (fun i => i.2.2.val) l z
  have hf (z : ℂ) (hz : z ∉ L.lattice) (hp : z + v ∉ L.lattice) : AnalyticAt ℂ f z :=
    analyticAt_const.mul (h_first v hvL c (fun i => i.1.val) (fun i => i.2.1.val)
      (fun i => i.2.2.val) l z hz hp).1
  have hjet (z : ℂ) (hz : z ∉ L.lattice) (hp : z + v ∉ L.lattice) (j : ℕ)
      (hbefore : ∀ k < j, iteratedDeriv k F (z + v) = 0) :
      iteratedDeriv j f z = Q ^ (5 * l) *
        (2 * (L.weierstrassP v - L.weierstrassP z)) ^ (3 * l) * iteratedDeriv j F (z + v) := by
    dsimp only [f]
    rw [iteratedDeriv_const_mul_field,
      (h_first v hvL c (fun i => i.1.val) (fun i => i.2.1.val)
        (fun i => i.2.2.val) l z hz hp).2 j hbefore]
    ring
  have hlocal (z : ℂ) (hz : z ∉ L.lattice) (hp : z + v ∉ L.lattice) :
      G =ᶠ[𝓝 z] fun w => D.sigma w ^ (15 * l) * f w := by
    have hnear := (continuousAt_id.add_const v).eventually
      (L.isClosed_lattice.isOpen_compl.mem_nhds hp)
    filter_upwards [L.isClosed_lattice.isOpen_compl.mem_nhds hz, hnear] with w hw hwp
    exact hGeq w hw hwp
  have hnodes (x : ℂ) (hx : x ∈ Γ.image (fun z => z - v)) :
      x ∉ L.lattice ∧ x + v ∉ L.lattice := by
    rcases Finset.mem_image.mp hx with ⟨y, hy, rfl⟩
    exact ⟨p2m_mc_18_translated_shifted_grid_regular L ω u₁ u₂ h_grid _ _ y v hy hv,
      by simpa using h_grid.shifted_grid_regular _ y hy⟩
  have hfj : ∀ x ∈ Γ.image (fun z => z - v), ∀ j < m + 1, iteratedDeriv j f x = 0 := by
    intro x hx j hj
    obtain ⟨hxL, hxp⟩ := hnodes x hx
    rcases Finset.mem_image.mp hx with ⟨y, hy, rfl⟩
    rw [hjet (y - v) hxL hxp j (by
      intro k hk
      simpa using hzero y hy k (hk.trans hj))]
    simp only [sub_add_cancel]
    rw [hzero y hy j hj, mul_zero]
  have hbasep : u₁ / 2 + v ∉ L.lattice := by
    apply h_grid.shifted_grid_regular ![3 * s, 3 * s, 3 * q]
    exact Finset.mem_image.mpr ⟨v, hv, add_comm _ _⟩
  have hbeforef : ∀ j < n, iteratedDeriv j f (u₁ / 2) = 0 := by
    intro j hj
    rw [hjet _ hbase hbasep j (fun k hk => hbefore k (hk.trans hj)), hbefore j hj, mul_zero]
  have houter : ∀ z ∈ sphere (0 : ℂ) R, ‖G z‖ ≤ Real.exp ((11 * B + 112) * (N : ℝ) ^ 2) := by
    intro z hz
    exact hGbound z (by simpa only [mem_sphere, dist_zero_right] using le_of_eq hz)
  have hdec' := hdec v hvr f G (fun z => D.sigma z ^ (15 * l)) hG
    (fun x hx => hf x (hnodes x hx).1 (hnodes x hx).2)
    (fun x _ => (D.entire.analyticAt x).pow _)
    (fun x hx => hlocal x (hnodes x hx).1 (hnodes x hx).2)
    hfj houter (u₁ / 2) hbaseR n hn
  have hinv' : ‖D.sigma (u₁ / 2) ^ (15 * l)‖⁻¹ ≤ Real.exp ((11 * B + 112) * (N : ℝ) ^ 2) := by
    apply hinv.trans (Real.exp_le_exp.mpr ?_)
    nlinarith [sq_nonneg (N : ℝ), mul_nonneg hB (sq_nonneg (N : ℝ))]
  have hsmall := hdec'.2 (hf _ hbase hbasep) ((D.entire.analyticAt _).pow _)
    (hlocal _ hbase hbasep) hbeforef (pow_ne_zero _ (h_sigma_nonzero _ hbase)) hinv'
  rwa [hjet _ hbase hbasep n hbefore] at hsmall


-- Retained proved helper calculations: from_nonlattice_jet_decay
open scoped Polynomial
open Filter

open WeierstrassEllipticZeta

set_option maxHeartbeats 800000

/-- Absorb all arithmetic denominator factors into the nonlattice first-derivative bound. -/
private theorem p2m_mc_19_nonlattice_arithmetic_first_derivative_decay
    (L : PeriodPair) (ω u₁ u₂ θ ν : ℂ)
    (h_parameters : AuxiliaryGridParameterData L ω u₁ u₂)
    (h_denominators : ∀ C : ℕ,
    ∃ B : ℝ, 0 < B ∧ ∀ (L : PeriodPair) (v z : ℂ) (N s : ℕ),
      1 ≤ Real.log N → ∀ P : NonlatticeCoordinatePresentation L θ ν v z C N s,
        let E : Fin 8 → ℂ := fun a =>
          MvPolynomial.eval₂ (Int.castRingHom ℂ) ![θ, ν] (P.denominator a)
        let Q := E 1 * E 2 * E 3
        Q ≠ 0 ∧
          ‖Q‖ + ‖Q * weierstrassZeta L v‖ + ‖Q * L.weierstrassP v‖ +
              ‖Q * L.derivWeierstrassP v‖ ≤ Real.exp (B * ((s : ℝ) ^ 2 + Real.log N)) ∧
          ∀ m l n : ℕ,
            ‖E 0 ^ m * (E 4 * E 5 * E 6 * E 7) ^ (m + 5 * l + n)‖ ≤
              Real.exp (B * ((m : ℝ) * Real.log N + m + 5 * l + n)))
    (h_nonlattice_decay : ∀ B K : ℝ, 0 ≤ B → 0 < K → ∀ᶠ N : ℕ in Filter.atTop,
      let m := auxiliaryL0 N
      let l := auxiliaryL N
      let s := auxiliaryS N
      ∀ c : Fin (m + 1) × Fin (l + 1) × Fin (l + 1) → ℂ,
        (∑ i, ‖c i‖) ≤ Real.exp (B * N) →
        let F : ℂ → ℂ := fun w => ∑ i, c i * w ^ i.1.val *
          L.weierstrassP w ^ i.2.1.val * weierstrassZeta L w ^ i.2.2.val
        (∀ x ∈ shiftedAuxiliaryGrid u₁ u₂ ω ![s, s, auxiliaryS3 N],
          ∀ j < m + 1, iteratedDeriv j F x = 0) →
        ∀ v ∈ auxiliaryGrid u₁ u₂ ω ![3 * s, 3 * s, 3 * auxiliaryS3 N],
          v ∉ L.lattice → ∀ Q : ℂ,
            ‖Q‖ + ‖Q * weierstrassZeta L v‖ + ‖Q * L.weierstrassP v‖ +
              ‖Q * L.derivWeierstrassP v‖ ≤ Real.exp (B * ((s : ℝ) ^ 2 + Real.log N)) →
            ∀ n : ℕ, (n : ℝ) ≤ K * m →
              (∀ j < n, iteratedDeriv j F (u₁ / 2 + v) = 0) →
              ‖Q ^ (5 * l) * (2 * (L.weierstrassP v - L.weierstrassP (u₁ / 2))) ^
                (3 * l) * iteratedDeriv n F (u₁ / 2 + v)‖ ≤
                  Real.exp (-(N : ℝ) ^ 2 * Real.log N / 73728)) :
    ∀ (C : ℕ) (B K : ℝ), 0 ≤ B → 0 < K → ∀ᶠ N : ℕ in Filter.atTop,
      let m := auxiliaryL0 N
      let l := auxiliaryL N
      let s := auxiliaryS N
      ∀ c : Fin (m + 1) × Fin (l + 1) × Fin (l + 1) → ℂ,
        (∑ i, ‖c i‖) ≤ Real.exp (B * N) →
        let F : ℂ → ℂ := fun w => ∑ i, c i * w ^ i.1.val *
          L.weierstrassP w ^ i.2.1.val * weierstrassZeta L w ^ i.2.2.val
        (∀ x ∈ shiftedAuxiliaryGrid u₁ u₂ ω ![s, s, auxiliaryS3 N],
          ∀ j < m + 1, iteratedDeriv j F x = 0) →
        ∀ v ∈ auxiliaryGrid u₁ u₂ ω ![3 * s, 3 * s, 3 * auxiliaryS3 N],
          v ∉ L.lattice →
            ∀ P : NonlatticeCoordinatePresentation L θ ν v (u₁ / 2) C N s,
              ∀ n : ℕ, (n : ℝ) ≤ K * m →
                (∀ j < n, iteratedDeriv j F (u₁ / 2 + v) = 0) →
                ‖(∏ a, MvPolynomial.eval₂ (Int.castRingHom ℂ) ![θ, ν]
                    (P.denominator a) ^ nonlatticeJetWeight m l n a) *
                  (2 * (L.weierstrassP v - L.weierstrassP (u₁ / 2))) ^ (3 * l) *
                  iteratedDeriv n F (u₁ / 2 + v)‖ ≤
                    Real.exp (-(N : ℝ) ^ 2 * Real.log N / 147456) := by
  intro C B K hB hK
  obtain ⟨A, hA, hden⟩ := h_denominators C
  have hlog : ∀ᶠ N : ℕ in atTop, 1 ≤ Real.log N :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1
  obtain ⟨N₀, hN₀⟩ := exists_nat_ge (147456 * A * (7 + K))
  filter_upwards [h_parameters 1 zero_lt_one,
    h_nonlattice_decay (B + A) K (by positivity) hK, hlog,
    eventually_ge_atTop N₀] with N hpar hdec hlogN hN
  let m := auxiliaryL0 N
  let l := auxiliaryL N
  let s := auxiliaryS N
  rcases hpar with ⟨hm, hl, hs, hq, hsq, hdim, hlow, hupp, hml, hls, hrest⟩
  have hlm : l ≤ m := (Nat.le_mul_of_pos_right l (by positivity : 0 < s ^ 2)).trans hls
  have hmN : (m : ℝ) ≤ N := by
    have := mul_le_mul_of_nonneg_left hlogN (Nat.cast_nonneg m)
    dsimp [m] at *
    nlinarith only [this, hml]
  have hlm' : (l : ℝ) ≤ m := by exact_mod_cast hlm
  have hlN : (l : ℝ) ≤ N := hlm'.trans hmN
  dsimp only
  intro c hc hzero v hv hvl P n hn hbefore
  let E : Fin 8 → ℂ := fun a =>
    MvPolynomial.eval₂ (Int.castRingHom ℂ) ![θ, ν] (P.denominator a)
  let Q : ℂ := E 1 * E 2 * E 3
  let W : ℂ := E 0 ^ m * (E 4 * E 5 * E 6 * E 7) ^ (m + 5 * l + n)
  obtain ⟨hQne, hQ, hW⟩ := hden L v (u₁ / 2) N s hlogN P
  have hT : 0 ≤ (s : ℝ) ^ 2 + Real.log N := by positivity
  have hc' : (∑ i, ‖c i‖) ≤ Real.exp ((B + A) * N) :=
    hc.trans (Real.exp_le_exp.mpr (by nlinarith [mul_nonneg hA.le (Nat.cast_nonneg N : (0 : ℝ) ≤ N)]))
  have hQ' : ‖Q‖ + ‖Q * weierstrassZeta L v‖ + ‖Q * L.weierstrassP v‖ +
      ‖Q * L.derivWeierstrassP v‖ ≤ Real.exp ((B + A) * ((s : ℝ) ^ 2 + Real.log N)) :=
    hQ.trans (Real.exp_le_exp.mpr (by nlinarith [mul_nonneg hB hT]))
  have hsmall := hdec c hc' hzero v hv hvl Q hQ' n hn hbefore
  have hnN : (n : ℝ) ≤ K * N := hn.trans (mul_le_mul_of_nonneg_left hmN hK.le)
  have hW' : ‖W‖ ≤ Real.exp (A * (7 + K) * N) := by
    apply (hW m l n).trans
    apply Real.exp_le_exp.mpr
    have ht : (m : ℝ) * Real.log N + m + 5 * l + n ≤ (7 + K) * N := by
      nlinarith only [hml, hmN, hlN, hnN]
    exact (mul_le_mul_of_nonneg_left ht hA.le).trans_eq (by ring)
  have hsplit : (∏ a, E a ^ nonlatticeJetWeight m l n a) = W * Q ^ (5 * l) := by
    simp [Fin.prod_univ_succ, nonlatticeJetWeight, W, Q, mul_pow]
    ring
  rw [show (∏ a, MvPolynomial.eval₂ (Int.castRingHom ℂ) ![θ, ν]
      (P.denominator a) ^ nonlatticeJetWeight m l n a) = W * Q ^ (5 * l) from hsplit,
    mul_assoc W, mul_assoc W, norm_mul]
  calc
    _ ≤ Real.exp (A * (7 + K) * N) *
        Real.exp (-(N : ℝ) ^ 2 * Real.log N / 73728) :=
      mul_le_mul hW' hsmall (norm_nonneg _) (Real.exp_pos _).le
    _ = Real.exp (A * (7 + K) * N - (N : ℝ) ^ 2 * Real.log N / 73728) := by
      rw [← Real.exp_add]; congr 1; ring
    _ ≤ Real.exp (-(N : ℝ) ^ 2 * Real.log N / 147456) := by
      apply Real.exp_le_exp.mpr
      have ht : 147456 * A * (7 + K) ≤ (N : ℝ) :=
        hN₀.trans (by exact_mod_cast hN)
      have h1 := mul_le_mul_of_nonneg_right ht (Nat.cast_nonneg N)
      have h2 := mul_le_mul_of_nonneg_left hlogN (sq_nonneg (N : ℝ))
      nlinarith only [h1, h2]

end WeierstrassEllipticZeta

open WeierstrassEllipticZeta

theorem _root_.WeierstrassEllipticZeta.exists_complex_auxiliary_systems_on_regular_grids
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

  have h_jets := p2m_mc_0_cleared_addition_jet_data L h_zeta_deriv h_zeta_addition h_wp_addition

  have h_jet_height := p2m_mc_1_cleared_addition_height

  have h_arithmetic := p2m_mc_2_arithmetic_jets_of_polynomial_jets L h_jets h_jet_height

  have hg_zero : g.eval₂ (Polynomial.aeval θ).toRingHom ν = 0 :=
    (hg_kernel g).mpr (dvd_refl g)
  have h_reduced := p2m_mc_3_reduced_arithmetic_jets_of_arithmetic_jets L h_arithmetic θ ν
    g hg_monic hg_degree hg_zero

  have h_jet_systems := p2m_mc_4_reduced_jet_systems_of_reduced_jets L h_zeta_deriv h_zeta_addition
    θ ν g h_reduced

  have h_interpolation := p2m_mc_5_grid_interpolation_of_regular_grid L ω u₁ u₂ h_grid

  have h_regularization := p2m_mc_6_elliptic_regularization_of_interpolation L ω u₁ u₂ h_grid
    h_zeta_deriv h_interpolation

  have h_cleared_entire := p2m_mc_7_cleared_addition_entire_data L ω u₁ u₂ h_grid h_zeta_deriv
    h_zeta_addition h_wp_addition h_interpolation

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
  have h_period_jets := p2m_mc_8_period_arithmetic_jet_systems L ω (u₁ / 2) θ ν
    h_zeta_deriv hperiod hregular g hg_monic hg_degree hg_zero d hd hdata

  have h_parameters := p2m_mc_9_auxiliary_grid_parameter_data L ω u₁ u₂ h_grid

  have h_decay := p2m_mc_10_auxiliary_grid_decay_data L ω u₁ u₂ h_grid h_parameters

  have h_period_bounds := bounded_auxiliary_period_jet_systems L ω u₁ u₂ θ ν g d
    h_parameters h_period_jets

  have h_nonlattice_bounds := bounded_auxiliary_nonlattice_jet_systems L ω u₁ u₂ θ ν g
    h_parameters h_jet_systems

  have h_coordinates := auxiliary_nonlattice_coordinate_presentations L ω u₁ u₂ h_grid
    h_zeta_deriv h_zeta_addition h_wp_addition θ ν g d hd h_data
  have h_grid_matrices := assemble_auxiliary_grid_jet_matrices L ω u₁ u₂ θ ν g d
    h_grid h_parameters h_coordinates h_nonlattice_bounds h_period_bounds

  obtain ⟨D, A, hA, hbound⟩ := exists_elliptic_sigma_quadratic_growth L
  obtain ⟨S, hS, hrel, _, _, _, hgrowth⟩ :=
    sigma_regularized_coordinates_entire L D h_zeta_deriv
  have hA' : 0 < 9 * A + 24 := by linarith
  have hbound' (z : ℂ) : ‖D.sigma z‖ ≤ Real.exp ((9 * A + 24) * (1 + ‖z‖ ^ 2)) := by
    apply (hbound z).trans
    apply Real.exp_le_exp.mpr
    nlinarith [sq_nonneg ‖z‖, mul_nonneg hA.le (sq_nonneg ‖z‖)]
  have h_factors_entire := hS
  have h_factors_eq := hrel
  have h_factor_growth := hgrowth A hA.le hbound
  have h_sigma_growth := hbound'
  have hA : 0 < 9 * A + 24 := hA'
  let A := 9 * A + 24

  obtain ⟨hne, hinv⟩ := sigma_period_inverse_bounds L D h_zeta_deriv
  obtain ⟨_, hscaled⟩ := p2m_mc_15_sigma_auxiliary_regularizer_inverse_bounds_from_progressions
    L ω u₁ u₂ h_grid h_parameters D hne hinv
  have h_sigma_nonzero := hne
  have h_sigma_inverse := hscaled

  have hfirst := elliptic_auxiliary_first_derivative_decay L ω u₁ u₂ h_grid h_parameters
    h_decay h_zeta_deriv h_regularization D S h_factors_entire h_factors_eq A hA
    h_sigma_growth h_factor_growth h_sigma_nonzero
  have hperiod := p2m_mc_16_period_auxiliary_arithmetic_decay_from_first_derivative
    L ω u₁ u₂ h_parameters D (Polynomial.aeval θ d) h_sigma_inverse hfirst
  have h_period_decay := hperiod

  have houter := p2m_mc_17_scaled_cleared_auxiliary_outer_bound L ω u₁ u₂ h_parameters D.sigma S
    A hA h_sigma_growth h_factor_growth (by
      intro ι inst v hv c l₀ l₂ l₃ M₀ M h₀ h₂ h₃
      exact cleared_addition_entire_growth_weighted L h_zeta_addition h_wp_addition
        D.sigma S (fun z _ => D.entire.analyticAt z) h_factors_entire h_factors_eq
        v hv c l₀ l₂ l₃ M₀ M h₀ h₂ h₃)
  have h_scaled_cleared_growth := houter

  have hsmall := p2m_mc_18_scaled_nonlattice_first_derivative_decay L ω u₁ u₂ h_grid h_parameters
    h_decay D h_sigma_nonzero (h_sigma_inverse.mono fun N h => h.1)
    h_scaled_cleared_growth (by
      intro ι inst v hv c l₀ l₂ l₃ M z hz hp
      exact cleared_auxiliary_first_derivative L h_zeta_deriv v hv c l₀ l₂ l₃ M z hz hp)
  have h_nonlattice_decay := hsmall

  have hsmall := p2m_mc_19_nonlattice_arithmetic_first_derivative_decay L ω u₁ u₂ θ ν
    h_parameters (nonlattice_common_denominator_bounds θ ν) h_nonlattice_decay
  have h_arithmetic_nonlattice_decay := hsmall

  exact complex_auxiliary_systems_of_bounded_grid_derivatives L ω u₁ u₂ θ ν g d
    hg_degree hd h_grid h_parameters h_zeta_deriv h_zeta_addition h_grid_matrices
    h_period_decay h_arithmetic_nonlattice_decay
    (auxiliary_grid_bounded_nonzero_derivative L ω u₁ u₂ h_grid)
end

end MultiplicityCompactStep9

-- Assembly: WeierstrassEllipticZeta.exists_reduced_complex_auxiliary_systems
namespace MultiplicityCompactStep10
open _root_.WeierstrassEllipticZeta _root_.TranscendenceTheory

noncomputable section

namespace WeierstrassEllipticZeta

private theorem integer_zeta_shift (L : PeriodPair) (ω : ℂ) (hω : ω ∈ L.lattice)
    (n : ℤ) (z : ℂ) (hz : z ∉ L.lattice) :
    weierstrassZeta L (z + n * ω) =
      weierstrassZeta L z + n * zetaQuasiPeriod L ω := by
  have hreg (k : ℤ) : z + k * ω ∉ L.lattice := by
    intro hm
    apply hz
    simpa [zsmul_eq_mul] using L.lattice.sub_mem hm (L.lattice.smul_mem k hω)
  induction n using Int.induction_on with
  | zero => simp
  | succ n ih =>
    have hs := weierstrassZeta_add_period L ω (z + n * ω) hω (hreg n)
    have heq : z + (((n : ℤ) + 1 : ℤ) : ℂ) * ω = z + n * ω + ω := by
      push_cast
      ring
    rw [heq, hs]
    push_cast at ih ⊢
    rw [ih]
    ring
  | pred n ih =>
    let k : ℤ := -(n : ℤ)
    have hs := weierstrassZeta_add_period L ω
      (z + ((k - 1 : ℤ) : ℂ) * ω) hω (hreg (k - 1))
    have heq : z + ((k - 1 : ℤ) : ℂ) * ω + ω = z + k * ω := by
      push_cast
      ring
    change weierstrassZeta L (z + k * ω) =
      weierstrassZeta L z + k * zetaQuasiPeriod L ω at ih
    rw [heq, ih] at hs
    change weierstrassZeta L (z + (k - 1 : ℤ) * ω) =
      weierstrassZeta L z + (k - 1 : ℤ) * zetaQuasiPeriod L ω
    push_cast
    push_cast at hs
    linear_combination -hs

private theorem regular_auxiliary_grid_data
    (L : PeriodPair) (ω u₁ u₂ : ℂ)
    (hω : ω ∈ L.lattice)
    (h_independent : LinearIndependent ℚ ![u₁, u₂, ω])
    (h_intersection : Submodule.span ℤ {u₁, u₂} ⊓ L.lattice = ⊥) :
    RegularAuxiliaryGridData L ω u₁ u₂ := by
  classical
  obtain ⟨hinj, hlat, hreg, hcong⟩ :=
    TranscendenceTheory.integer_grid_geometry L.lattice ω u₁ u₂
      hω h_independent h_intersection
  have hfinite (A : Fin 3 → ℕ) : Function.Injective
      (fun m : (i : Fin 3) → Fin (A i) ↦
        integerGridPoint u₁ u₂ ω (fun i ↦ (m i : ℕ))) := by
    intro m n hmn
    have heq := hinj hmn
    funext i
    apply Fin.ext
    exact_mod_cast congrFun heq i
  have hcard (A : Fin 3 → ℕ) : (auxiliaryGrid u₁ u₂ ω A).card = ∏ i, A i := by
    rw [auxiliaryGrid, Finset.card_image_of_injective _ (hfinite A)]
    simp [Fintype.card_pi]
  refine ⟨hinj, hlat, hcong, hreg, hcard, ?_, ?_, ?_, ?_⟩
  · intro A
    rw [shiftedAuxiliaryGrid,
      Finset.card_image_of_injective _ (add_left_injective (u₁ / 2)), hcard]
  · intro A z hz
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨m, _, rfl⟩ := Finset.mem_image.mp hw
    exact hreg _
  · intro A z hz
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨m, _, rfl⟩ := Finset.mem_image.mp hw
    have hm (i : Fin 3) : ((m i : ℕ) : ℝ) ≤ A i := by
      exact_mod_cast (m i).isLt.le
    calc
      ‖integerGridPoint u₁ u₂ ω (fun i ↦ (m i : ℕ)) + u₁ / 2‖ ≤
          ‖integerGridPoint u₁ u₂ ω (fun i ↦ (m i : ℕ))‖ + ‖u₁ / 2‖ :=
        norm_add_le _ _
      _ ≤ (‖(((m 0 : ℕ) : ℂ) * u₁)‖ + ‖(((m 1 : ℕ) : ℂ) * u₂)‖ +
          ‖(((m 2 : ℕ) : ℂ) * ω)‖) + ‖u₁ / 2‖ := by
        dsimp [integerGridPoint]
        push_cast
        gcongr
        exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ = ((m 0 : ℕ) : ℝ) * ‖u₁‖ + ((m 1 : ℕ) : ℝ) * ‖u₂‖ +
          ((m 2 : ℕ) : ℝ) * ‖ω‖ + ‖u₁‖ / 2 := by
        simp
      _ ≤ _ := by gcongr <;> exact (m _).isLt.le
  · intro z n hz
    have hn : (n : ℂ) * ω ∈ L.lattice := by
      simpa [zsmul_eq_mul] using L.lattice.smul_mem n hω
    exact ⟨L.weierstrassP_add_coe z ⟨_, hn⟩,
      L.derivWeierstrassP_add_coe z ⟨_, hn⟩, integer_zeta_shift L ω hω n z hz⟩

end WeierstrassEllipticZeta

open WeierstrassEllipticZeta
open scoped Polynomial

theorem _root_.WeierstrassEllipticZeta.exists_reduced_complex_auxiliary_systems
    (L : PeriodPair) (ω u₁ u₂ : ℂ)
    (hω_ne : ω ≠ 0) (hω_period : ω ∈ L.lattice)
    (h_linearIndependent : LinearIndependent ℚ ![u₁, u₂, ω])
    (h_intersection : Submodule.span ℤ {u₁, u₂} ⊓ L.lattice = ⊥)
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
  have h_grid := regular_auxiliary_grid_data L ω u₁ u₂ hω_period
    h_linearIndependent h_intersection
  exact exists_complex_auxiliary_systems_on_regular_grids L ω u₁ u₂ h_grid
    h_zeta_deriv h_zeta_addition h_wp_addition θ hθ ν g hg_monic hg_degree
    hg_kernel d hd h_data
end

end MultiplicityCompactStep10

-- Assembly: WeierstrassEllipticZeta.exists_bounded_auxiliary_systems
namespace MultiplicityCompactStep11
open _root_.WeierstrassEllipticZeta _root_.TranscendenceTheory

open WeierstrassEllipticZeta Polynomial Filter
open scoped Polynomial

theorem _root_.WeierstrassEllipticZeta.exists_bounded_auxiliary_systems
    (L : PeriodPair) (ω u₁ u₂ : ℂ)
    (hω_ne : ω ≠ 0) (hω_period : ω ∈ L.lattice)
    (h_linearIndependent : LinearIndependent ℚ ![u₁, u₂, ω])
    (h_intersection : Submodule.span ℤ {u₁, u₂} ⊓ L.lattice = ⊥)
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
    (hν : ∃ f : ℤ[X][X], f.Monic ∧ f.eval₂ (Polynomial.aeval θ).toRingHom ν = 0)
    (d : ℤ[X]) (hd : Polynomial.aeval θ d ≠ 0)
    (h_data : ∀ i : Fin 18, ∃ p : ℤ[X][X],
      p.eval₂ (Polynomial.aeval θ).toRingHom ν = Polynomial.aeval θ d *
        (![L.g₂/4, L.g₃/4, ω, zetaQuasiPeriod L ω, u₁/2, u₂,
        weierstrassZeta L (u₁/2), L.weierstrassP (u₁/2),
        L.derivWeierstrassP (u₁/2), deriv L.derivWeierstrassP (u₁/2),
        L.weierstrassP u₁, L.derivWeierstrassP u₁, deriv L.derivWeierstrassP u₁,
        weierstrassZeta L u₁, L.weierstrassP u₂, L.derivWeierstrassP u₂,
        deriv L.derivWeierstrassP u₂, weierstrassZeta L u₂] i)) :
    ∃ a c : ℝ, 0 < a ∧ 0 < c ∧
      ∀ᶠ N : ℕ in Filter.atTop,
        Nonempty (TranscendenceTheory.BoundedBivariateSystem θ ν a c N) := by
  obtain ⟨g, hg_monic, hg_degree, hg_kernel, hreduce⟩ :=
    TranscendenceTheory.exists_reduced_bivariate_model θ ν hθ hν
  have h_data_reduced : ∀ i : Fin 18, ∃ p : ℤ[X][X],
      p.natDegree < g.natDegree ∧
      p.eval₂ (Polynomial.aeval θ).toRingHom ν = Polynomial.aeval θ d *
        (![L.g₂/4, L.g₃/4, ω, zetaQuasiPeriod L ω, u₁/2, u₂,
        weierstrassZeta L (u₁/2), L.weierstrassP (u₁/2),
        L.derivWeierstrassP (u₁/2), deriv L.derivWeierstrassP (u₁/2),
        L.weierstrassP u₁, L.derivWeierstrassP u₁, deriv L.derivWeierstrassP u₁,
        weierstrassZeta L u₁, L.weierstrassP u₂, L.derivWeierstrassP u₂,
        deriv L.derivWeierstrassP u₂, weierstrassZeta L u₂] i) := by
    intro i
    obtain ⟨p, hp⟩ := h_data i
    obtain ⟨q, ⟨hq_degree, hq_eval⟩, _⟩ := hreduce p
    exact ⟨q, hq_degree, hq_eval.trans hp⟩
  obtain ⟨a, c, ha, hc, hsystems⟩ :=
    exists_reduced_complex_auxiliary_systems L ω u₁ u₂ hω_ne hω_period
      h_linearIndependent h_intersection h_zeta_deriv h_zeta_addition h_wp_addition
      θ hθ ν g hg_monic hg_degree hg_kernel d hd h_data_reduced
  refine ⟨a, c, ha, hc, ?_⟩
  filter_upwards [hsystems] with N hN
  obtain ⟨S, hred⟩ := hN
  exact TranscendenceTheory.bounded_system_of_complex_auxiliary_system θ ν g
    (fun p hp => (hg_kernel p).mp hp) a c N S hred

end MultiplicityCompactStep11

-- Assembly: WeierstrassEllipticZeta.small_bivariate_values_of_integral_auxiliary_data
namespace MultiplicityCompactStep12
open _root_.WeierstrassEllipticZeta _root_.TranscendenceTheory

open WeierstrassEllipticZeta Polynomial

theorem _root_.WeierstrassEllipticZeta.small_bivariate_values_of_integral_auxiliary_data
    (L : PeriodPair) (ω u₁ u₂ : ℂ)
    (hω_ne : ω ≠ 0) (hω_period : ω ∈ L.lattice)
    (h_linearIndependent : LinearIndependent ℚ ![u₁, u₂, ω])
    (h_intersection : Submodule.span ℤ {u₁, u₂} ⊓ L.lattice = ⊥)
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
    (hν : ∃ f : ℤ[X][X], f.Monic ∧ f.eval₂ (Polynomial.aeval θ).toRingHom ν = 0)
    (d : ℤ[X]) (hd : Polynomial.aeval θ d ≠ 0)
    (h_data : ∀ i : Fin 18, ∃ p : ℤ[X][X],
      p.eval₂ (Polynomial.aeval θ).toRingHom ν = Polynomial.aeval θ d *
        (![L.g₂/4, L.g₃/4, ω, zetaQuasiPeriod L ω, u₁/2, u₂,
        weierstrassZeta L (u₁/2), L.weierstrassP (u₁/2),
        L.derivWeierstrassP (u₁/2), deriv L.derivWeierstrassP (u₁/2),
        L.weierstrassP u₁, L.derivWeierstrassP u₁, deriv L.derivWeierstrassP u₁,
        weierstrassZeta L u₁, L.weierstrassP u₂, L.derivWeierstrassP u₂,
        deriv L.derivWeierstrassP u₂, weierstrassZeta L u₂] i)) :
    ∃ A c : ℝ, 0 < A ∧ 0 < c ∧
        ∀ᶠ N : ℕ in Filter.atTop, ∃ P : ℤ[X][X],
          (P.natDegree : ℝ) ≤ A * N ∧
          (∀ j, ((P.coeff j).natDegree : ℝ) ≤ A * N) ∧
          (∀ j k, |((P.coeff j).coeff k : ℝ)| ≤ Real.exp (A * N)) ∧
          P.eval₂ (Polynomial.aeval θ).toRingHom ν ≠ 0 ∧
          ‖P.eval₂ (Polynomial.aeval θ).toRingHom ν‖ ≤
            Real.exp (-c * (N : ℝ) ^ 2 * Real.log N) := by
  apply TranscendenceTheory.small_values_of_bounded_bivariate_systems θ ν
  exact exists_bounded_auxiliary_systems L ω u₁ u₂ hω_ne hω_period
    h_linearIndependent h_intersection h_zeta_deriv h_zeta_addition h_wp_addition
    θ hθ ν hν d hd h_data

end MultiplicityCompactStep12

-- Assembly: WeierstrassEllipticZeta.small_bivariate_values_of_algebraic_values
namespace MultiplicityCompactStep13
open _root_.WeierstrassEllipticZeta _root_.TranscendenceTheory

open WeierstrassEllipticZeta Polynomial

theorem _root_.WeierstrassEllipticZeta.small_bivariate_values_of_algebraic_values
    (L : PeriodPair) (ω u₁ u₂ : ℂ)
    (hω_ne : ω ≠ 0) (hω_period : ω ∈ L.lattice)
    (h_linearIndependent : LinearIndependent ℚ ![u₁, u₂, ω])
    (h_intersection : Submodule.span ℤ {u₁, u₂} ⊓ L.lattice = ⊥)
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
    (h_values : ∀ i, IsAlgebraic (Algebra.adjoin ℚ {θ})
      (theoremOneValues L ω u₁ u₂ i)) :
    ∃ ν : ℂ,
      (∃ f : ℤ[X][X], f.Monic ∧ f.eval₂ (Polynomial.aeval θ).toRingHom ν = 0) ∧
      ∃ A c : ℝ, 0 < A ∧ 0 < c ∧
        ∀ᶠ N : ℕ in Filter.atTop, ∃ P : ℤ[X][X],
          (P.natDegree : ℝ) ≤ A * N ∧
          (∀ j, ((P.coeff j).natDegree : ℝ) ≤ A * N) ∧
          (∀ j k, |((P.coeff j).coeff k : ℝ)| ≤ Real.exp (A * N)) ∧
          P.eval₂ (Polynomial.aeval θ).toRingHom ν ≠ 0 ∧
          ‖P.eval₂ (Polynomial.aeval θ).toRingHom ν‖ ≤
            Real.exp (-c * (N : ℝ) ^ 2 * Real.log N) := by
  have hu₁ : u₁ ∉ L.lattice := by
    intro h
    have hm : u₁ ∈ Submodule.span ℤ {u₁, u₂} ⊓ L.lattice :=
      ⟨Submodule.subset_span (by simp), h⟩
    rw [h_intersection, Submodule.mem_bot] at hm
    exact (h_linearIndependent.ne_zero 0) hm
  have hu₂ : u₂ ∉ L.lattice := by
    intro h
    have hm : u₂ ∈ Submodule.span ℤ {u₁, u₂} ⊓ L.lattice :=
      ⟨Submodule.subset_span (by simp), h⟩
    rw [h_intersection, Submodule.mem_bot] at hm
    exact (h_linearIndependent.ne_zero 1) hm
  have halg := algebraic_auxiliary_values L ω u₁ u₂ θ hu₁ hu₂ h_values
  obtain ⟨ν, hν, d, hd, h_data⟩ :=
    TranscendenceTheory.exists_integral_generator_and_common_denominator θ hθ
      (![L.g₂/4, L.g₃/4, ω, zetaQuasiPeriod L ω, u₁/2, u₂,
        weierstrassZeta L (u₁/2), L.weierstrassP (u₁/2),
        L.derivWeierstrassP (u₁/2), deriv L.derivWeierstrassP (u₁/2),
        L.weierstrassP u₁, L.derivWeierstrassP u₁, deriv L.derivWeierstrassP u₁,
        weierstrassZeta L u₁, L.weierstrassP u₂, L.derivWeierstrassP u₂,
        deriv L.derivWeierstrassP u₂, weierstrassZeta L u₂]) halg
  refine ⟨ν, hν, ?_⟩
  exact small_bivariate_values_of_integral_auxiliary_data
    L ω u₁ u₂ hω_ne hω_period h_linearIndependent h_intersection
    h_zeta_deriv h_zeta_addition h_wp_addition θ hθ ν hν d hd h_data

end MultiplicityCompactStep13

-- Assembly: WeierstrassEllipticZeta.small_integral_elements_of_algebraic_values
namespace MultiplicityCompactStep14
open _root_.WeierstrassEllipticZeta _root_.TranscendenceTheory

open Polynomial Module Filter WeierstrassEllipticZeta
open scoped Polynomial

theorem _root_.WeierstrassEllipticZeta.small_integral_elements_of_algebraic_values
    (L : PeriodPair) (ω u₁ u₂ : ℂ)
    (hω_ne : ω ≠ 0) (hω_period : ω ∈ L.lattice)
    (h_linearIndependent : LinearIndependent ℚ ![u₁, u₂, ω])
    (h_intersection : Submodule.span ℤ {u₁, u₂} ⊓ L.lattice = ⊥)
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
    (h_values : ∀ i, IsAlgebraic (Algebra.adjoin ℚ {θ})
      (theoremOneValues L ω u₁ u₂ i)) :
    ∃ (S : Subring ℂ) (hθS : θ ∈ S) (d : ℕ),
      letI : Algebra ℤ[X] S := (Polynomial.aeval (⟨θ, hθS⟩ : S)).toAlgebra
      ∃ b : Module.Basis (Fin (d + 1)) ℤ[X] S, b 0 = 1 ∧
        ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
          ∀ᶠ N : ℕ in Filter.atTop, ∃ x : S, x ≠ 0 ∧
            (∀ i, ((b.repr x i).natDegree : ℝ) ≤ C * N) ∧
            (∀ i k, |((b.repr x i).coeff k : ℝ)| ≤ Real.exp (C * N)) ∧
            ‖(x : ℂ)‖ ≤ Real.exp (-c * (N : ℝ) ^ 2 * Real.log N) := by
  obtain ⟨ν, hν, A, c, hA, hc, hsmall⟩ :=
    small_bivariate_values_of_algebraic_values L ω u₁ u₂ hω_ne hω_period
      h_linearIndependent h_intersection h_zeta_deriv h_zeta_addition h_wp_addition θ hθ h_values
  have hθZ : Transcendental ℤ θ := hθ.restrictScalars (algebraMap ℤ ℚ).injective_int
  exact TranscendenceTheory.small_integral_coordinates_of_bivariate_values θ ν hθZ hν A c hA hc hsmall

end MultiplicityCompactStep14

-- Assembly: WeierstrassEllipticZeta.small_polynomials_of_algebraic_values
namespace MultiplicityCompactStep15
open _root_.WeierstrassEllipticZeta _root_.TranscendenceTheory

open Polynomial Module Filter WeierstrassEllipticZeta
open scoped Polynomial

theorem _root_.WeierstrassEllipticZeta.small_polynomials_of_algebraic_values
    (L : PeriodPair) (ω u₁ u₂ : ℂ)
    (hω_ne : ω ≠ 0) (hω_period : ω ∈ L.lattice)
    (h_linearIndependent : LinearIndependent ℚ ![u₁, u₂, ω])
    (h_intersection : Submodule.span ℤ {u₁, u₂} ⊓ L.lattice = ⊥)
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
    (h_values : ∀ i, IsAlgebraic (Algebra.adjoin ℚ {θ})
      (theoremOneValues L ω u₁ u₂ i)) :
    ∃ A : ℝ, 0 < A ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∃ p : ℤ[X],
        (p.natDegree : ℝ) ≤ A * N ∧
        (∀ k, |(p.coeff k : ℝ)| ≤ Real.exp (A * N)) ∧
        0 < ‖Polynomial.aeval θ p‖ ∧
        ‖Polynomial.aeval θ p‖ ≤ Real.exp (-10 * (A * N) ^ 2) := by
  obtain ⟨S, hθS, d, b, hb, C, c, hC, hc, hsmall⟩ :=
    small_integral_elements_of_algebraic_values L ω u₁ u₂ hω_ne hω_period
      h_linearIndependent h_intersection h_zeta_deriv h_zeta_addition h_wp_addition θ hθ h_values
  let : Algebra ℤ[X] S := (Polynomial.aeval (⟨θ, hθS⟩ : S)).toAlgebra
  have hθZ : Transcendental ℤ θ := hθ.restrictScalars (algebraMap ℤ ℚ).injective_int
  apply TranscendenceTheory.small_polynomials_of_small_integral_elements
    θ hθZ S.subtype _ d b hb C c hC hc hsmall
  intro p
  change (↑(Polynomial.aeval (⟨θ, hθS⟩ : S) p) : ℂ) = Polynomial.aeval θ p
  simpa using (Polynomial.aeval_algHom_apply (S.subtype.toIntAlgHom) (⟨θ, hθS⟩ : S) p).symm

end MultiplicityCompactStep15

-- Assembly: WeierstrassEllipticZeta.senthil_kumar_theorem_one
open Filter
open scoped Topology Polynomial

noncomputable section

open WeierstrassEllipticZeta

private theorem linear_small_polynomials_impossible
    (θ : ℂ) (hθ : Transcendental ℚ θ)
    (A : ℝ) (hA : 0 < A) (N₀ : ℕ)
    (hsmall : ∀ N : ℕ, N₀ ≤ N → ∃ p : ℤ[X],
      (p.natDegree : ℝ) ≤ A * N ∧
      (∀ k, |(p.coeff k : ℝ)| ≤ Real.exp (A * N)) ∧
      0 < ‖Polynomial.aeval θ p‖ ∧
      ‖Polynomial.aeval θ p‖ ≤ Real.exp (-10 * (A * N) ^ 2)) : False := by
  classical
  choose P hP using (fun n : ℕ => hsmall (n + (N₀ + 1)) (by omega))
  let d : ℕ → ℝ := fun n => A * (n + (N₀ + 1) : ℕ)
  have hd_pos : ∀ n, 0 < d n := by
    intro n
    dsimp [d]
    positivity
  have hd_strict : StrictMono d := by
    intro i j hij
    dsimp [d]
    apply mul_lt_mul_of_pos_left _ hA
    exact_mod_cast Nat.add_lt_add_right hij (N₀ + 1)
  have hd_unbounded : Tendsto d atTop atTop := by
    exact Tendsto.const_mul_atTop hA
      (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat (N₀ + 1)))
  have hd_growth : ∀ n, d (n + 1) ≤ 2 * d n := by
    intro n
    dsimp [d]
    push_cast
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hN : (0 : ℝ) ≤ N₀ := Nat.cast_nonneg N₀
    nlinarith
  have h_nonzero : ∀ n, Polynomial.aeval θ (P n) ≠ 0 := by
    intro n
    exact norm_pos_iff.mp (hP n).2.2.1
  have h_lower := TranscendenceTheory.gelfond_polynomial_sequence_lower_bound
    θ hθ 2 (by norm_num) d d hd_pos hd_pos hd_strict hd_strict
    hd_unbounded hd_unbounded hd_growth hd_growth P h_nonzero
    (fun n => (hP n).1) (fun n => (hP n).2.1)
  obtain ⟨n, hn⟩ := h_lower.exists
  have h_upper : Real.log ‖Polynomial.aeval θ (P n)‖ ≤ -10 * (d n) ^ 2 := by
    have hlog := Real.log_le_log (hP n).2.2.1 (hP n).2.2.2
    simpa only [Real.log_exp] using hlog
  have hcompare : -(2 * (2 : ℝ) + 1) * d n * (d n + d n) = -10 * (d n) ^ 2 := by
    ring
  rw [hcompare] at hn
  exact (not_lt_of_ge h_upper) hn

/-- The remaining arithmetic reduction uses the proved zeta and elliptic addition
identities. Its two open inputs are the auxiliary polynomial construction and
Gel'fond's polynomial-sequence criterion. -/
theorem solution (L : PeriodPair) (ω u₁ u₂ : ℂ)
    (hω_ne : ω ≠ 0)
    (hω_period : ω ∈ L.lattice)
    (h_linearIndependent : LinearIndependent ℚ ![u₁, u₂, ω])
    (h_intersection : Submodule.span ℤ {u₁, u₂} ⊓ L.lattice = ⊥) :
    HasAlgebraicallyIndependentPair (theoremOneValues L ω u₁ u₂) := by
  classical
  by_contra hpair
  obtain ⟨θ, hθ, h_values⟩ :=
    exists_transcendental_parameter_of_no_pair (theoremOneValues L ω u₁ u₂) hpair
  obtain ⟨A, hA, N₀, hsmall⟩ := small_polynomials_of_algebraic_values
    L ω u₁ u₂ hω_ne hω_period h_linearIndependent h_intersection
    (hasDerivAt_weierstrassZeta L) (zeta_addition_formula L) (wp_addition_formula L)
    θ hθ h_values
  exact linear_small_polynomials_impossible θ hθ A hA N₀ hsmall
end
