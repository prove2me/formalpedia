-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Advance50.P50.lemma2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T12:57:51.18348+00:00
-- url     : https://prove2.me/submissions/176846fe-7079-476d-a9e4-a594f6a3ee91

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P50
noncomputable section

open MeasureTheory ProbabilityTheory

open scoped ComplexConjugate ENNReal

open QAlgorithms.Papers.Independent.Advance50.P50

theorem solution {Omega : Type*} [MeasurableSpace Omega]
    (mu0 mu1 : Measure Omega) [IsProbabilityMeasure mu0] [IsProbabilityMeasure mu1]
    (X : Omega → ℝ) (hX : Measurable X) (c b1 b2 : ℝ)
    (hclass1 : ∀ᵐ w ∂mu1, X w = c)
    (hclass0 : ∀ᵐ w ∂mu0, X w ∈ Set.Icc b1 b2) :
    posteriorAt mu0 mu1 X c =
      (mu0 {w | X w = c}).toReal / (1 + (mu0 {w | X w = c}).toReal) := by
  have hmeas : MeasurableSet {w | X w = c} := hX (measurableSet_singleton c)
  have h1 : mu1 {w | X w = c} = 1 := by
    rw [← prob_compl_eq_zero_iff hmeas]
    rw [ae_iff] at hclass1
    simpa [Set.compl_setOf] using hclass1
  unfold posteriorAt
  rw [h1, ENNReal.toReal_one, add_comm]

end
