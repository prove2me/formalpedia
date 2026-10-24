-- Prove2me | solution 1 for PandoraBO.Private20261023.reservation_roots_strict_antitone
-- status  : ACCEPTED   (prove)
-- author  : @QianJaneXie
-- created : 2026-10-24T01:05:30.154604+00:00
-- url     : https://prove2.me/submissions/1e02312e-b6d9-442d-9b71-bc4f0c93344a

import Definitions.Def_PandoraBO_Model
import Mathlib.Tactic.Linarith

/-!
An independent analytic ingredient for monotone policy limits: increasing the
inspection-cost multiplier strictly decreases any corresponding finite
reservation roots. Existence of roots is not assumed globally in this lemma.
-/

set_option autoImplicit false

open MeasureTheory PandoraBO

private theorem improvement_integrable {n : ℕ} (M : Instance n)
    (i : Box n) (z : ℝ) :
    Integrable (fun y : ℝ => max (y - z) 0) (M.law i) := by
  letI : IsProbabilityMeasure (M.law i) := M.law_probability i
  exact ((M.reward_integrable i).sub (integrable_const z)).pos_part

theorem solution {n : ℕ} (M : Instance n) (i : Box n) (s t z w : ℝ)
    (hst : s < t)
    (hz : reservationRoot M i (s * M.cost i) z)
    (hw : reservationRoot M i (t * M.cost i) w) :
    w < z := by
  by_contra hn
  have hzw : z ≤ w := le_of_not_gt hn
  have hEI : expectedImprovement M i w ≤ expectedImprovement M i z :=
    integral_mono (improvement_integrable M i w) (improvement_integrable M i z)
      (fun y => max_le_max (sub_le_sub_left hzw y) le_rfl)
  change expectedImprovement M i z = s * M.cost i at hz
  change expectedImprovement M i w = t * M.cost i at hw
  rw [hz, hw] at hEI
  have hpositive : 0 < (t - s) * M.cost i :=
    mul_pos (sub_pos.mpr hst) (M.cost_positive i)
  nlinarith
