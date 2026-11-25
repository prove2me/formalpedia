-- Prove2me | solution 1 for PI.EF.Rect.rectInt_inv_sub_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:00:46.603798+00:00
-- url     : https://prove2.me/submissions/e94c3f7a-24e2-4ff5-9a9b-621a1921e4aa

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_RectIntEqZeroOfDifferentiableOn
import Theorems.Thm_PI_EF_Rect_rectInt_eq_zero_of_primitive
import Theorems.Thm_PI_EF_Rect_ne_of_mem_bdry_of_mem_open

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.EF PI.EF.Rect
open Complex MeasureTheory intervalIntegral Set Filter Topology Real
namespace PI.EF.Rect
theorem _root_.solution {z w p : ℂ} (hp : p ∈ rectOpen z w) :
    rectInt (fun s => ((s - p) ^ 2)⁻¹) z w = 0 := by
  apply rectInt_eq_zero_of_primitive (F := fun s => -(s - p)⁻¹)
  · intro s hs
    have hne : s - p ≠ 0 := sub_ne_zero.2 (ne_of_mem_bdry_of_mem_open hs hp)
    have hd := ((hasDerivAt_inv hne).comp_sub_const s p).neg
    rw [neg_neg] at hd
    exact hd
  · intro s hs
    have hne : s - p ≠ 0 := sub_ne_zero.2 (ne_of_mem_bdry_of_mem_open hs hp)
    exact ContinuousAt.inv₀ (by fun_prop) (pow_ne_zero 2 hne)
end PI.EF.Rect
