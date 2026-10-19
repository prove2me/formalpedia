-- Prove2me | solution 1 for PermanentRollout.permanent_rollout_uniform_output_chart_real_finrank_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:02.589874+00:00
-- url     : https://prove2.me/submissions/0a7a61b0-9538-413f-a932-017eb158afbc

import Mathlib
import Definitions.Def_Permanent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open Set Filter Module
open scoped BigOperators ENNReal
noncomputable section
namespace PermanentRollout
theorem _root_.solution
    (k m : ℕ) :
    finrank ℝ (permanentRolloutUniformOutputChartDomain k m) <
      finrank ℝ (Fin (k + 1) → Fin (m + 1) → ℂ) := by
  rw [finrank_real_of_complex, finrank_real_of_complex]
  change
    2 * finrank ℂ
      ((Fin k → ℂ) × (Fin (k + 1) → Fin m → ℂ)) <
      2 * finrank ℂ (Fin (k + 1) → Fin (m + 1) → ℂ)
  simp only [finrank_prod, finrank_pi_fintype,
    finrank_self, Fintype.card_fin,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  nlinarith
end PermanentRollout
