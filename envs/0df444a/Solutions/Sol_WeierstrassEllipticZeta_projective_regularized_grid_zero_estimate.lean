-- Prove2me | solution 1 for WeierstrassEllipticZeta.projective_regularized_grid_zero_estimate
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-08T14:41:52.825425+00:00
-- url     : https://prove2.me/submissions/126d961a-e46c-419a-be9a-c015bcf69907

import Theorems.Thm_WeierstrassEllipticZeta_auxiliary_grid_quotient_geometry
import Theorems.Thm_WeierstrassEllipticZeta_finite_set_projective_zero_estimate
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Definitions.Def_WeierstrassEllipticZeta_AuxiliaryGrids
import Definitions.Def_WeierstrassEllipticZeta_SigmaDifferential
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

open WeierstrassEllipticZeta
open scoped Pointwise

theorem solution
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
