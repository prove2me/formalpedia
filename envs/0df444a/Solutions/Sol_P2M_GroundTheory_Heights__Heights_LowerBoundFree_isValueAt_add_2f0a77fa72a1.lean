-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LowerBoundFree_isValueAt_add_2f0a77fa72a1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:18:29.685375+00:00
-- url     : https://prove2.me/submissions/5f79f2c1-1e18-4df9-8136-154e94eb3a64

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_FrameDefinitions_IsFrameOverLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_FrameDefinitions_Values
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_isMultiHomog_add_95ee52bfb1b9
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_isMultiHomog_mul_0d39b8f19b1f


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
open scoped Matrix
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {Ω : Type} [Field Ω]
omit [Fintype K]
namespace GroundTheory.Heights₂.Heights.LowerBoundFree
theorem _root_.solution {y : (Σ k, ι k) → Ω} {s t : Ω} {z : (Σ k, ι k) → ℂ} {v w : ℂ}
    (hv : IsValueAt y s z v) (hw : IsValueAt y t z w) : IsValueAt y (s + t) z (v + w) := by
  obtain ⟨d, g, h, hg, hh, hy, heq, hz0, rfl⟩ := hv
  obtain ⟨d', g', h', hg', hh', hy', heq', hz0', rfl⟩ := hw
  refine ⟨d + d', g * h' + g' * h, h * h', isMultiHomog_add (isMultiHomog_mul hg hh') ?_,
    isMultiHomog_mul hh hh', ?_, ?_, ?_, ?_⟩
  · rw [add_comm d d']; exact isMultiHomog_mul hg' hh
  · rw [map_mul]; exact mul_ne_zero hy hy'
  · rw [map_add, map_mul, map_mul, map_mul, heq, heq']; ring
  · rw [map_mul, map_mul]; exact mul_ne_zero hz0 hz0'
  · simp only [map_add, map_mul]
    field_simp
end GroundTheory.Heights₂.Heights.LowerBoundFree
