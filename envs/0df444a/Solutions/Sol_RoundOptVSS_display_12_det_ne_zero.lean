-- Prove2me | solution 1 for RoundOptVSS.display_12_det_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-17T09:34:07.674775+00:00
-- url     : https://prove2.me/submissions/e58263e1-ee7a-4959-90ef-1354b8fa31a2

import Mathlib
namespace RoundOptVSS

theorem display_12_det_ne_zero {𝔽 𝔼 : Type} [Field 𝔽] [Field 𝔼] [Algebra 𝔽 𝔼]
    (lam : 𝔼) (L : ℕ) (hlam : IsIntegral 𝔽 lam) (hL : (minpoly 𝔽 lam).natDegree = L)
    {r : ℕ} (A : Matrix (Fin r) (Fin r) 𝔽) (hr : r < L) :
    (lam • (1 : Matrix (Fin r) (Fin r) 𝔼) + A.map (algebraMap 𝔽 𝔼)).det ≠ 0 ∧
    ∀ v : Fin r → 𝔼, ∃! u : Fin r → 𝔼,
      (lam • (1 : Matrix (Fin r) (Fin r) 𝔼) + A.map (algebraMap 𝔽 𝔼)).mulVec u = v := by
  set M := lam • (1 : Matrix (Fin r) (Fin r) 𝔼) + A.map (algebraMap 𝔽 𝔼) with hM
  have hdet : M.det ≠ 0 := by
    have e : M = Matrix.scalar (Fin r) lam - (-A).map (algebraMap 𝔽 𝔼) := by
      rw [hM]; ext i j
      simp [Matrix.one_apply, Matrix.diagonal_apply]
    have e2 : M.det = Polynomial.aeval lam (-A).charpoly := by
      rw [e, ← Matrix.eval_charpoly, Matrix.charpoly_map, Polynomial.eval_map_algebraMap]
    intro h0
    rw [e2] at h0
    have hdvd := minpoly.dvd 𝔽 lam h0
    have hp0 : (-A).charpoly ≠ 0 := (Matrix.charpoly_monic _).ne_zero
    have := Polynomial.natDegree_le_of_dvd hdvd hp0
    rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin, hL] at this
    omega
  refine ⟨hdet, fun v => ?_⟩
  have hu : IsUnit M.det := isUnit_iff_ne_zero.mpr hdet
  refine ⟨M⁻¹.mulVec v, ?_, ?_⟩
  · simp only [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu, Matrix.one_mulVec]
  · intro u hu'
    rw [← hu', Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec]

end RoundOptVSS

theorem solution {𝔽 𝔼 : Type} [Field 𝔽] [Field 𝔼] [Algebra 𝔽 𝔼]
    (lam : 𝔼) (L : ℕ) (hlam : IsIntegral 𝔽 lam) (hL : (minpoly 𝔽 lam).natDegree = L)
    {r : ℕ} (A : Matrix (Fin r) (Fin r) 𝔽) (hr : r < L) :
    (lam • (1 : Matrix (Fin r) (Fin r) 𝔼) + A.map (algebraMap 𝔽 𝔼)).det ≠ 0 ∧
    ∀ v : Fin r → 𝔼, ∃! u : Fin r → 𝔼,
      (lam • (1 : Matrix (Fin r) (Fin r) 𝔼) + A.map (algebraMap 𝔽 𝔼)).mulVec u = v :=
  RoundOptVSS.display_12_det_ne_zero lam L hlam hL A hr
