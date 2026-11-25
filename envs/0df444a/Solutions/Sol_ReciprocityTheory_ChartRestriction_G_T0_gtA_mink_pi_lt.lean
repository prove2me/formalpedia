-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.gtA_mink_pi_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:30:13.159198+00:00
-- url     : https://prove2.me/submissions/f5f081fe-7d1f-44d7-9166-400488639563

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
theorem _root_.solution {n : ℕ} (B : Basis (Fin n) ℝ (Fin n → ℝ)) {t : ℝ} (ht : 0 < t)
    (h : |(Matrix.of B).det| < t ^ n) :
    ∃ x ∈ span ℤ (Set.range B), x ≠ 0 ∧ ‖x‖ < t := by
  haveI := gtA_countable B
  have fund := ZSpan.isAddFundamentalDomain B volume
  obtain ⟨x, hx0, hxs⟩ := MeasureTheory.exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure
    (L := (span ℤ (Set.range B)).toAddSubgroup) fund (s := Metric.ball (0 : Fin n → ℝ) t) (fun y hy => by simpa using hy)
    (convex_ball (0 : Fin n → ℝ) t) (by
      have h2 : (2 : ENNReal) ^ n = ENNReal.ofReal ((2 : ℝ) ^ n) := by
        rw [ENNReal.ofReal_pow (by norm_num)]
        simp
      rw [ZSpan.volume_fundamentalDomain B, Real.volume_pi_ball 0 ht, Module.finrank_fin_fun,
        Fintype.card_fin, h2, ← ENNReal.ofReal_mul (abs_nonneg _),
        ENNReal.ofReal_lt_ofReal_iff (by positivity), mul_pow, mul_comm ((2 : ℝ) ^ n)]
      exact mul_lt_mul_of_pos_right h (by positivity))
  refine ⟨x, x.2, fun h0 => hx0 (Subtype.ext h0), ?_⟩
  simpa using hxs
end ReciprocityTheory.ChartRestriction.G.T0
