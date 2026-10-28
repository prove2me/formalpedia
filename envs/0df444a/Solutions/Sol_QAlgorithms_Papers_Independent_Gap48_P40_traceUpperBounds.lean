-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P40.traceUpperBounds
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-10-26T22:37:51.27799+00:00
-- url     : https://prove2.me/submissions/1ee24282-7229-40b1-bafa-924b778b71b2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P17_referenceMinimumUpperBound
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P40

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder Topology Matrix.Norms.L2Operator

open Filter MeasureTheory Asymptotics

open QAlgorithms

open QAlgorithms.Papers.Independent.Dependency50.P21 (relativeEntropy)

open QAlgorithms.Papers.Independent.Information100.P50 (IsUINorm)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

open QAlgorithms.Papers.Independent.Information100.P60 (copies)

open QAlgorithms.Papers.Independent.Information100.P44 (Mat)

namespace QAlgorithms.Papers.Independent.Gap48.P40

/-- Reduction of Theorem 6 (55)-(56) of quant-ph/0503218 to Corollary 1 (19)-(20) of
arXiv:1105.2656, whose proof corrects the original one. -/
theorem tub_main {d : ℕ} (hd : 0 < d) (rho sigma : Mat d)
    (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma)
    (hbeta : 0 < minEigenvalue sigma) :
    let beta := minEigenvalue sigma
    let T := traceNorm (rho - sigma) / 2
    (T ≤ beta → relativeEntropy rho sigma ≤ ((traceSmallBound beta T : ℝ) : EReal)) ∧
    (beta ≤ T → T ≤ 1 - beta → relativeEntropy rho sigma ≤
      (((beta + T) * Real.log ((beta + T) / beta) : ℝ) : EReal)) := by
  haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have h := QAlgorithms.Papers.Independent.Support50.P17.referenceMinimumUpperBound
    rho sigma hrho hsigma hbeta
  have hT : traceDistance rho sigma = traceNorm (rho - sigma) / 2 := by
    unfold traceDistance; ring
  simp only [hT] at h
  dsimp only
  have hb : minEigenvalue sigma ≠ 0 := hbeta.ne'
  have e1 : (minEigenvalue sigma + traceNorm (rho - sigma) / 2) / minEigenvalue sigma =
      1 + traceNorm (rho - sigma) / 2 / minEigenvalue sigma := by field_simp
  have e2 : (minEigenvalue sigma - traceNorm (rho - sigma) / 2) / minEigenvalue sigma =
      1 - traceNorm (rho - sigma) / 2 / minEigenvalue sigma := by field_simp
  refine ⟨fun hle => ?_, fun hle _ => ?_⟩
  · simpa only [traceSmallBound, e1, e2] using h.1 hle
  · simpa only [e1] using h.2 hle

end QAlgorithms.Papers.Independent.Gap48.P40

open QAlgorithms.Papers.Independent.Gap48.P40 in
theorem solution {d : ℕ} (hd : 0 < d) (rho sigma : Mat d)
    (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma)
    (hbeta : 0 < minEigenvalue sigma) :
    let beta := minEigenvalue sigma
    let T := traceNorm (rho - sigma) / 2
    (T ≤ beta → relativeEntropy rho sigma ≤ ((traceSmallBound beta T : ℝ) : EReal)) ∧
    (beta ≤ T → T ≤ 1 - beta → relativeEntropy rho sigma ≤
      (((beta + T) * Real.log ((beta + T) / beta) : ℝ) : EReal)) :=
  tub_main hd rho sigma hrho hsigma hbeta

end
