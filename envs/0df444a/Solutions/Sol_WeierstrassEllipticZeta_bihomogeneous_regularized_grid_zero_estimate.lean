-- Prove2me | solution 1 for WeierstrassEllipticZeta.bihomogeneous_regularized_grid_zero_estimate
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-08T14:20:00.855222+00:00
-- url     : https://prove2.me/submissions/a6c8e430-ee51-4262-9d21-b2ad9f6de115

import Theorems.Thm_WeierstrassEllipticZeta_sigma_projective_coordinates_entire
import Theorems.Thm_WeierstrassEllipticZeta_projective_regularized_grid_zero_estimate
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Tactic.FinCases
import Definitions.Def_WeierstrassEllipticZeta_AuxiliaryGrids
import Definitions.Def_WeierstrassEllipticZeta_SigmaDifferential
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

open WeierstrassEllipticZeta

theorem solution
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
