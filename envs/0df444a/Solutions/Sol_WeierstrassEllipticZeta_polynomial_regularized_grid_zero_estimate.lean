-- Prove2me | solution 1 for WeierstrassEllipticZeta.polynomial_regularized_grid_zero_estimate
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-08T13:52:57.272999+00:00
-- url     : https://prove2.me/submissions/1178e8de-a37d-4374-af1b-66f5d70801e8

import Theorems.Thm_TranscendenceTheory_bihomogeneous_lift_four_variables
import Theorems.Thm_WeierstrassEllipticZeta_bihomogeneous_regularized_grid_zero_estimate
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
