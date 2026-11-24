-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LowerBound_CuspWeightBound_proof_31f7e20228db
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:49:24.936786+00:00
-- url     : https://prove2.me/submissions/3ffd8635-9095-4c74-96db-4fd61aef6ca0

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_CountingLowerBound_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_CountingLowerBound_PCuspWeightBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBound
open Real
namespace GroundTheory.Heights₂.Heights.LowerBound
namespace CuspWeightBound
theorem _root_.solution : CuspWeightBound.Statement := by
  intro f j' ρ rd lam NI covol h
  have hf : (1 : ℝ) ≤ f := by exact_mod_cast h.one_le_f
  have hj : (1 : ℝ) ≤ j' := by exact_mod_cast h.one_le_j'
  have hρ : (1 : ℝ) ≤ ρ := by exact_mod_cast h.one_le_ρ
  have hρj : (ρ : ℝ) ≤ j' := by exact_mod_cast h.ρ_le_j'
  have hrd := h.one_le_rd
  have hlam := h.lam_pos
  have hNI := h.NI_pos
  have h2fρ : (0 : ℝ) < 2 * f * ρ := by positivity
  have hsq : 0 < √(2 * f * ρ : ℝ) := Real.sqrt_pos.mpr h2fρ

  have hmk : (lam / √(2 * f * ρ : ℝ)) ^ (2 * f * ρ) ≤ NI * rd ^ (f * ρ) :=
    h.covol_eq ▸ h.minkowski
  have hrdp : (0 : ℝ) < rd ^ (f * ρ) := by positivity
  have hlog := Real.log_le_log (by positivity) hmk
  rw [Real.log_pow, Real.log_mul hNI.ne' hrdp.ne', Real.log_pow,
    Real.log_div hlam.ne' hsq.ne', Real.log_sqrt h2fρ.le] at hlog
  push_cast at hlog

  have hρbound : -log NI ≤ f * ρ * (2 * log (1 / lam) + log (2 * f * ρ * rd)) := by
    have hrd0 : rd ≠ 0 := by positivity
    rw [one_div, Real.log_inv, Real.log_mul h2fρ.ne' hrd0]
    nlinarith

  have hB : 0 ≤ 2 * max 0 (log (1 / lam)) + log (2 * f * j' * rd) := by
    have : 0 ≤ log (2 * f * j' * rd) := by
      have h1 : (1 : ℝ) ≤ f * j' := one_le_mul_of_one_le_of_one_le hf hj
      have h2 : (1 : ℝ) ≤ f * j' * rd := one_le_mul_of_one_le_of_one_le h1 hrd
      exact Real.log_nonneg (by linarith)
    have : 0 ≤ max 0 (log (1 / lam)) := le_max_left _ _
    linarith
  have hin : 2 * log (1 / lam) + log (2 * f * ρ * rd) ≤
      2 * max 0 (log (1 / lam)) + log (2 * f * j' * rd) := by
    have h1 : log (1 / lam) ≤ max 0 (log (1 / lam)) := le_max_right _ _
    have h2 : log (2 * f * ρ * rd) ≤ log (2 * f * j' * rd) :=
      Real.log_le_log (by positivity) (by gcongr)
    linarith
  calc -log NI ≤ f * ρ * (2 * log (1 / lam) + log (2 * f * ρ * rd)) := hρbound
    _ ≤ f * ρ * (2 * max 0 (log (1 / lam)) + log (2 * f * j' * rd)) := by
        gcongr
    _ ≤ f * j' * (2 * max 0 (log (1 / lam)) + log (2 * f * j' * rd)) := by
        gcongr
end CuspWeightBound
end GroundTheory.Heights₂.Heights.LowerBound
