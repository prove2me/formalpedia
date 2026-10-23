-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P27.coherence_score_identity
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T06:41:24.442807+00:00
-- url     : https://prove2.me/submissions/90eb81a6-d6cc-44da-850f-33f18a2b0886

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P27

noncomputable section

open scoped ComplexConjugate ComplexOrder

attribute [local instance] Classical.decEq Classical.propDecidable

open QAlgorithms QAlgorithms.Papers.Independent.Information100.P27

theorem solution {d : ℕ} (hd : 0 < d)
    (r theta : Matrix (Fin d) (Fin d) ℂ) (hr : IsDensityMatrix r)
    (hp : ∀ i, 0 < (r i i).re) (htheta : IsDensityMatrix theta)
    (mu : ℝ) (hmu : 0 ≤ mu) :
    (1 + mu) * coherence (schur (correlation r) theta) - mu * coherence theta =
      matrixScore mu (correlation r) theta := by
  have hdiag : ∀ i, (schur (correlation r) theta) i i = theta i i := by
    intro i
    simp only [schur, correlation]
    have hre : ((r i i).re : ℂ) = r i i := hr.1.isHermitian.coe_re_apply_self i
    rw [Real.sqrt_mul_self (hp i).le, hre, div_self, one_mul]
    rw [← hre]
    exact_mod_cast (hp i).ne'
  simp only [coherence, matrixScore, hdiag]
  ring
