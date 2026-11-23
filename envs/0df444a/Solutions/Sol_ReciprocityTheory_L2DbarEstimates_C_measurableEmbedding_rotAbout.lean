-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.C.measurableEmbedding_rotAbout
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:36:38.167794+00:00
-- url     : https://prove2.me/submissions/7b3cfa1f-83fc-497f-b10c-6bc11a724139

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_Circle
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_MeasurableEmbeddingRotAbout

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.C
open MeasureTheory Metric Set Filter Topology Complex
open scoped ENNReal
namespace ReciprocityTheory.L2DbarEstimates.C
theorem _root_.solution {n : ℕ} (c : V n) {a : ℂ} (ha : ‖a‖ = 1) :
    MeasurableEmbedding (rotAbout c a) := by
  have ha0 : a ≠ 0 := by rintro rfl; simp at ha
  let h : V n ≃ₜ V n :=
    { toFun := rotAbout c a
      invFun := fun z => c + a⁻¹ • (z - c)
      left_inv := fun z => by simp [rotAbout, smul_smul, inv_mul_cancel₀ ha0]
      right_inv := fun z => by simp [rotAbout, smul_smul, mul_inv_cancel₀ ha0]
      continuous_toFun := by unfold rotAbout; fun_prop
      continuous_invFun := by fun_prop }
  exact h.measurableEmbedding
end ReciprocityTheory.L2DbarEstimates.C
