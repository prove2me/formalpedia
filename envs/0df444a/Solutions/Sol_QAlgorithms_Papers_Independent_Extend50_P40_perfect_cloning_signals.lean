-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Extend50.P40.perfect_cloning_signals
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-11T20:52:46.190905+00:00
-- url     : https://prove2.me/submissions/dec2f917-1b57-4fc7-8161-60a0eeda7216

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P40
open QAlgorithms.Papers.Independent.Extend50.P40
noncomputable section



open QAlgorithms

open scoped Matrix ComplexOrder ComplexConjugate BigOperators Topology

open MeasureTheory Filter

open scoped Matrix.Norms.Frobenius

open QAlgorithms.Papers.Independent.Dependency50.P12 (sigma)

open QAlgorithms.Papers.Independent.Dependency50.P48 (pureFidelity)

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Support21.P16
  (CloneMap IsBoseInputChannel coherentTensor tensorWithIdentity canonicalCloner
   HasBoseOutput HasBlackCowCoefficient canonicalCoefficient oneMixed)

open QAlgorithms.Papers.Independent.Renew46.P45
  (TensorMat boseProjector siteObservable)

open QAlgorithms.Papers.Independent.Information100.P58 (Word)

/-- I.C.1, PDF p.3: Herbert's two hypothetical cloned mixtures give different
probabilities on outcome 01, without assuming existence of a physical perfect cloner. -/
theorem solution :
    let rx := (1 / 2 : ℂ) •
      (pureDensity (tensorVec (equator 0) (equator 0)) +
       pureDensity (tensorVec (equator Real.pi) (equator Real.pi)))
    let rz := (1 / 2 : ℂ) • (pureDensity (ket ((0, 0) : (Fin 2 × Fin 2))) + pureDensity (ket ((1, 1) : (Fin 2 × Fin 2))))
    densityProb rx (0, 1) = 1 / 4 ∧ densityProb rz (0, 1) = 0 ∧ rx ≠ rz := by
  classical
  let rx := (1 / 2 : ℂ) •
    (pureDensity (tensorVec (equator 0) (equator 0)) +
     pureDensity (tensorVec (equator Real.pi) (equator Real.pi)))
  let rz := (1 / 2 : ℂ) •
    (pureDensity (ket ((0, 0) : Fin 2 × Fin 2)) +
     pureDensity (ket ((1, 1) : Fin 2 × Fin 2)))
  change densityProb rx (0, 1) = 1 / 4 ∧ densityProb rz (0, 1) = 0 ∧ rx ≠ rz
  have he : Complex.exp (Complex.I * (Real.pi : ℂ)) = -1 := by
    rw [mul_comm, Complex.exp_pi_mul_I]
  have hi : (Real.sqrt 2)⁻¹ ^ 4 = (1 / 4 : ℝ) := by
    rw [show (4 : ℕ) = 2 * 2 by decide, pow_mul, inv_pow,
      Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hx : densityProb rx (0, 1) = 1 / 4 := by
    norm_num [rx, densityProb, pureDensity, tensorVec, equator, he,
      ← Complex.ofReal_inv, div_eq_mul_inv]
    ring_nf
    norm_num [hi]
  have hz : densityProb rz (0, 1) = 0 := by
    norm_num [rz, densityProb, pureDensity, ket, EuclideanSpace.single_apply]
  refine ⟨hx, hz, ?_⟩
  intro h
  have heq := congrArg (fun A => densityProb A (0, 1)) h
  rw [hx, hz] at heq
  norm_num at heq
