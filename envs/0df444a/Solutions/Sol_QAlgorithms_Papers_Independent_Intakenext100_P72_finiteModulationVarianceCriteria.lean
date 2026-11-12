-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakenext100.P72.finiteModulationVarianceCriteria
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-11T19:26:41.298519+00:00
-- url     : https://prove2.me/submissions/3247739f-8fc7-4360-90f7-f0f41942d694

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P72

open Filter

open scoped Topology

namespace Aux_FMVC

theorem key (a D N0 : ℝ) (hD : 0 < D) (hN : 0 < N0) : N0 / D > a * N0 ↔ a * D < 1 := by
  rw [gt_iff_lt, lt_div_iff₀ hD]
  have e : a * N0 * D = (a * D) * N0 := by ring
  rw [e]
  exact mul_lt_iff_lt_one_left hN

end Aux_FMVC

open QAlgorithms.Papers.Independent.Intakenext100.P72 in
theorem solution
    (V N0 Gx Gp chix chip s : ℝ)
    (hV : 1 ≤ V) (hN0 : 0 < N0) (hGx : 0 < Gx) (hGp : 0 < Gp)
    (hchix : 0 ≤ chix) (hchip : 0 ≤ chip)
    (hslo : 1 / V ≤ s) (hshi : s ≤ V) :
    (eveVarianceExpression Gp chip V N0 > aliceVarianceExpression Gx chix s N0 ↔
      (Gx * chix + Gx * s) * (Gp * chip + Gp / V) < 1) ∧
    (eveVarianceExpression Gx chix V N0 > aliceVarianceExpression Gp chip s N0 ↔
      (Gp * chip + Gp * s) * (Gx * chix + Gx / V) < 1) ∧
    ((eveVarianceExpression Gp chip V N0 > aliceVarianceExpression Gx chix s N0 ∨
      eveVarianceExpression Gx chix V N0 > aliceVarianceExpression Gp chip s N0) ↔
      ((Gx * chix + Gx * s) * (Gp * chip + Gp / V) < 1 ∨
       (Gp * chip + Gp * s) * (Gx * chix + Gx / V) < 1)) ∧
    (Gx = Gp → chix = chip →
      ((eveVarianceExpression Gp chip V N0 > aliceVarianceExpression Gx chix s N0 ∨
        eveVarianceExpression Gx chix V N0 > aliceVarianceExpression Gp chip s N0) ↔
        varianceProduct Gx chix V s < 1)) := by
  have hVpos : 0 < 1 / V := by
    have : (0 : ℝ) < V := by linarith
    positivity
  have c1 : eveVarianceExpression Gp chip V N0 > aliceVarianceExpression Gx chix s N0 ↔
      (Gx * chix + Gx * s) * (Gp * chip + Gp / V) < 1 := by
    unfold eveVarianceExpression aliceVarianceExpression
    have e : (Gx * chix + Gx * s) * (Gp * chip + Gp / V) =
        Gx * (chix + s) * (Gp * (chip + 1 / V)) := by ring
    rw [e]
    exact Aux_FMVC.key _ _ _ (mul_pos hGp (by linarith)) hN0
  have c2 : eveVarianceExpression Gx chix V N0 > aliceVarianceExpression Gp chip s N0 ↔
      (Gp * chip + Gp * s) * (Gx * chix + Gx / V) < 1 := by
    unfold eveVarianceExpression aliceVarianceExpression
    have e : (Gp * chip + Gp * s) * (Gx * chix + Gx / V) =
        Gp * (chip + s) * (Gx * (chix + 1 / V)) := by ring
    rw [e]
    exact Aux_FMVC.key _ _ _ (mul_pos hGx (by linarith)) hN0
  refine ⟨c1, c2, or_congr c1 c2, ?_⟩
  intro hG hc
  subst hG
  subst hc
  rw [or_self, c1] <;> exact Iff.rfl
