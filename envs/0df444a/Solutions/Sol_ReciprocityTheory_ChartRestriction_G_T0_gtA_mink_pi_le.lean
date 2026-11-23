-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.gtA_mink_pi_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:04:48.30493+00:00
-- url     : https://prove2.me/submissions/2fe74354-28ef-49fc-81ac-4d6cb5f9f238

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_TransferenceA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_gtA_countable

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open MeasureTheory Module Submodule
namespace ReciprocityTheory.ChartRestriction.G.T0
theorem _root_.solution {n : ℕ} (hn : 0 < n) (B : Basis (Fin n) ℝ (Fin n → ℝ)) {t : ℝ}
    (ht : 0 < t) (h : |(Matrix.of B).det| ≤ t ^ n) :
    ∃ x ∈ span ℤ (Set.range B), x ≠ 0 ∧ ‖x‖ ≤ t := by
  haveI := gtA_countable B
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have fund := ZSpan.isAddFundamentalDomain B volume
  obtain ⟨x, hx0, hxs⟩ := MeasureTheory.exists_ne_zero_mem_lattice_of_measure_mul_two_pow_le_measure
    (L := (span ℤ (Set.range B)).toAddSubgroup) fund (s := Metric.closedBall (0 : Fin n → ℝ) t) (fun y hy => by simpa using hy)
    (convex_closedBall (0 : Fin n → ℝ) t) (isCompact_closedBall (0 : Fin n → ℝ) t) (by
      have h2 : (2 : ENNReal) ^ n = ENNReal.ofReal ((2 : ℝ) ^ n) := by
        rw [ENNReal.ofReal_pow (by norm_num)]
        simp
      rw [ZSpan.volume_fundamentalDomain B, Real.volume_pi_closedBall 0 ht.le, Module.finrank_fin_fun,
        Fintype.card_fin, h2, ← ENNReal.ofReal_mul (abs_nonneg _)]
      apply ENNReal.ofReal_le_ofReal
      rw [mul_pow, mul_comm ((2 : ℝ) ^ n)]
      exact mul_le_mul_of_nonneg_right h (by positivity))
  refine ⟨x, x.2, fun h0 => hx0 (Subtype.ext h0), ?_⟩
  simpa using hxs
end ReciprocityTheory.ChartRestriction.G.T0
