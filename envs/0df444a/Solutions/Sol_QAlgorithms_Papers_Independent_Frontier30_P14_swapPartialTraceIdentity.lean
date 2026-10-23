-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Frontier30.P14.swapPartialTraceIdentity
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T08:05:42.446181+00:00
-- url     : https://prove2.me/submissions/20de339b-b99e-4bc1-b78b-947c165ab91f

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P14

noncomputable section

open scoped BigOperators NNReal ENNReal

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33

open QAlgorithms.Papers.Independent.Dependency50.P39 (displacementMatrix)

open QAlgorithms.Papers.Independent.Frontier30.P14 in
theorem solution (Theta : (Matrix (ℕ × ℕ) (ℕ × ℕ) ℂ))
    (htrace : IsTraceClass Theta) :
    productCoeff (partialRight (swapCoefficients Theta)) (identityCoeff ℕ) =
      swapCoefficients (productCoeff (identityCoeff ℕ) (partialLeft Theta)) := by
  funext p q
  simp only [productCoeff, partialRight, partialLeft, swapCoefficients]
  exact mul_comm _ _

end
