-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P20.unitResourceCone
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T08:08:24.571026+00:00
-- url     : https://prove2.me/submissions/d27333e3-128d-48e9-a311-bdb94c87e0a7

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P20
noncomputable section

open QAlgorithms.Papers.Independent.Claimed50.P20

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

open Filter

open QAlgorithms.Papers.Independent.Information100.P08 (Ensemble PureEnsemble channelHolevo)

open QAlgorithms.Papers.Independent.Information100.P62 (tensorChannel)

open QAlgorithms.Papers.Independent.Dependency50.P23 (IsHadamard)

open QAlgorithms.Papers.Independent.Dependency50.P41 (qubitErasure)

open QAlgorithms.Papers.Independent.Information100.P27 (qubitDephasing)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Section 5, PDF p.7 (13): exact algebraic characterization of the unit resource cone. -/
theorem solution (r : Rate) :
    r ∈ unitCone ↔ rateConstraints ![0, 0, 0] r := by
  constructor
  · rintro ⟨a, b, c, ha, hb, hc, rfl⟩
    refine ⟨?_, ?_, ?_⟩ <;>
      simp [Matrix.cons_val_zero, Matrix.cons_val_one] <;> linarith
  · rintro ⟨h1, h2, h3⟩
    simp at h1 h2 h3
    refine ⟨-(r 0 + 2 * r 1) / 2, -(r 1 + r 2) / 2, -(r 0 + r 1 + r 2) / 2,
      by linarith, by linarith, by linarith, ?_⟩
    ext i
    fin_cases i <;> simp <;> ring

end
