-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intake100.P64.collisionCoefficient_classicalCompatibility
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-11T22:28:49.511167+00:00
-- url     : https://prove2.me/submissions/7633295d-5b19-41f1-8f9f-e70fcab502f4

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P64

noncomputable section

open MeasureTheory Filter

open scoped BigOperators ENNReal NNReal Topology

open QAlgorithms.Papers.Independent.Claimed50.P39 (rising)

open QAlgorithms.Papers.Independent.Intake100.P64 in
theorem solution (d : CollisionData)
    (p P Q : Momentum) :
    Complex.normSq (collisionCoefficient d p P Q) = prefactor d.parameters Q *
      crossSection d
        (transverseRelative d.parameters p P Q - (1 / 2 : ℝ) • Q)
        (transverseRelative d.parameters p P Q + (1 / 2 : ℝ) • Q) *
      d.gas.value (gasArgument d.parameters p P Q) := by
  by_cases hQ : Q = 0
  · have h0 : prefactor d.parameters Q = 0 := by
      unfold prefactor
      rw [if_pos hQ]
    unfold collisionCoefficient
    rw [if_pos hQ, h0]
    simp
  · have hpre : 0 ≤ prefactor d.parameters Q := by
      unfold prefactor
      rw [if_neg hQ]
      exact div_nonneg (mul_nonneg d.parameters.density_pos.le d.parameters.m_pos.le)
        (by positivity)
    unfold collisionCoefficient crossSection
    rw [if_neg hQ, Complex.normSq_mul, Complex.normSq_mul, Complex.normSq_ofReal,
      Complex.normSq_ofReal, Real.mul_self_sqrt hpre,
      Real.mul_self_sqrt (d.gas.nonnegative _)]

end
