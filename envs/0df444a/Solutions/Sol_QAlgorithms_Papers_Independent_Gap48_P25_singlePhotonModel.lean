-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P25.singlePhotonModel
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-21T23:15:29.793048+00:00
-- url     : https://prove2.me/submissions/cb369296-eb36-43df-8a37-0aa58c3ffc24

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P25

open QAlgorithms.Papers.Independent.Gap48.P25
noncomputable section


open scoped BigOperators ComplexConjugate

open Filter

open QAlgorithms.Papers.Independent.Claimed50.P08 (classicalEntropy)

/-- Eq.(35), PDF p.29: ideal single-photon model identity, with honest detection
rate, negligible dark counts, information cost h(Q) and optimal EC. -/
theorem solution (nu t tB eta Q : ℝ) (hnu : 0 < nu)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) (htB : tB ∈ Set.Icc (0 : ℝ) 1)
    (heta : eta ∈ Set.Icc (0 : ℝ) 1) (hQ : Q ∈ Set.Icc (0 : ℝ) 1) :
    signedRate (nu*t*tB*eta) (QAlgorithms.binEntropy2 Q) (QAlgorithms.binEntropy2 Q) =
      nu*t*tB*eta*(1-2*QAlgorithms.binEntropy2 Q) ∧
    max (signedRate (nu*t*tB*eta) (QAlgorithms.binEntropy2 Q) (QAlgorithms.binEntropy2 Q)) 0 =
      nu*t*tB*eta*max (1-2*QAlgorithms.binEntropy2 Q) 0 := by
  have hR : 0 ≤ nu*t*tB*eta :=
    mul_nonneg (mul_nonneg (mul_nonneg hnu.le ht.1) htB.1) heta.1
  have e1 : signedRate (nu*t*tB*eta) (QAlgorithms.binEntropy2 Q) (QAlgorithms.binEntropy2 Q) =
      nu*t*tB*eta*(1-2*QAlgorithms.binEntropy2 Q) := by unfold signedRate; ring
  refine ⟨e1, ?_⟩
  rw [e1, mul_max_of_nonneg _ _ hR, mul_zero]



