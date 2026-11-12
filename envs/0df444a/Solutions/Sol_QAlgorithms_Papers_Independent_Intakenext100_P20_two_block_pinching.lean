-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakenext100.P20.two_block_pinching
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-11T23:20:15.498966+00:00
-- url     : https://prove2.me/submissions/a25dd3f9-d80e-4a71-929b-471ac211eb07

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P20

noncomputable section

open scoped Matrix ENNReal ComplexOrder Topology

open QAlgorithms.Papers.Independent.Information100.P08 (IsPure)

open QAlgorithms.Papers.Independent.Information100.P47 (IsProbability)

open QAlgorithms.Papers.Independent.Information100.P53 (SpectralData)

open QAlgorithms.Papers.Independent.Gap48.P19 (shannonNats)

open QAlgorithms.Papers.Independent.Dependency50.P28 (classicalD)

attribute [local instance] Classical.propDecidable

open QAlgorithms.Papers.Independent.Intakenext100.P20 in
theorem solution {d : ℕ} (hd : 0 < d)
    (rho : Matrix (Fin d) (Fin d) ℂ) (hrho : QAlgorithms.IsDensityMatrix rho)
    (P : Matrix (Fin d) (Fin d) ℂ) (hself : Pᴴ = P) (hidempotent : P * P = P) :
    (P * rho * P + (1 - P) * rho * (1 - P) - (1 / 2 : ℂ) • rho).PosSemidef := by
  have hM : (P + P - 1)ᴴ = P + P - 1 := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_add, Matrix.conjTranspose_one, hself]
  have hid : (P + P - 1) * rho * (P + P - 1) =
      (P * rho * P + (1 - P) * rho * (1 - P)) + (P * rho * P + (1 - P) * rho * (1 - P)) - rho := by
    noncomm_ring
  have hE : P * rho * P + (1 - P) * rho * (1 - P) - (1 / 2 : ℂ) • rho =
      (1 / 2 : ℂ) • ((P + P - 1)ᴴ * rho * (P + P - 1)) := by
    rw [hM, hid, smul_sub, smul_add, ← add_smul]
    norm_num
  rw [hE]
  have hhalf : (0 : ℂ) ≤ 1 / 2 := by
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast <;> ring]
    exact Complex.zero_le_real.2 (by norm_num)
  exact (hrho.1.conjTranspose_mul_mul_same (P + P - 1)).smul hhalf

end
