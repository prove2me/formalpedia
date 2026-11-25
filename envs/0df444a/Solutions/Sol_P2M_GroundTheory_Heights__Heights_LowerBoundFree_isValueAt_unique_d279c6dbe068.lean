-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LowerBoundFree_isValueAt_unique_d279c6dbe068
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:40:17.314859+00:00
-- url     : https://prove2.me/submissions/62ea7208-b459-4610-abb0-71ce3b31f3cb

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_CoordinateIdeals_MemMCoordIdealOfAevalEqZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_FrameDefinitions_Metric
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_isMultiHomog_sub_d1cc7c10540b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_eval_eq_zero_of_mem_mcPts_db46e4f02c8a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_isMultiHomog_mul_0d39b8f19b1f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_mem_mCoordIdeal_of_aeval_eq_zero_09693c41a4b2


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {Ω : Type} [Field Ω]
namespace GroundTheory.Heights₂.Heights.LowerBoundFree
theorem _root_.solution {y : (Σ k, ι k) → Ω} {s : Ω} {z : (Σ k, ι k) → ℂ}
    (hz : z ∈ mcPts (mCoordIdeal y)) {v w : ℂ} (hv : IsValueAt y s z v) (hw : IsValueAt y s z w) :
    v = w := by
  obtain ⟨d, g, h, hg, hh, _, heq, hz0, rfl⟩ := hv
  obtain ⟨d', g', h', hg', hh', _, heq', hz0', rfl⟩ := hw
  have hsub : IsMultiHomog (g * h' - g' * h) (d + d') := by
    refine isMultiHomog_sub (isMultiHomog_mul hg hh') ?_
    rw [add_comm]
    exact isMultiHomog_mul hg' hh
  have h0 : aeval y (g * h' - g' * h) = 0 := by
    rw [map_sub, map_mul, map_mul, heq, heq']
    ring
  have := eval_eq_zero_of_mem_mcPts hz (mem_mCoordIdeal_of_aeval_eq_zero y hsub h0)
  simp only [map_sub, map_mul, sub_eq_zero] at this
  rw [div_eq_div_iff hz0 hz0', this]
end GroundTheory.Heights₂.Heights.LowerBoundFree
