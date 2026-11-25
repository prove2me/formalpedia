-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.PhSchurConv.Main.coef_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:42:53.823575+00:00
-- url     : https://prove2.me/submissions/9f1e773e-6ac8-48bc-b087-eab7160a4d0e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_PhSchurConv
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SchurConvolution_MapMulApply
import Theorems.Thm_PI_UnitaryGroupMassFormula_PhSchurConv_Main_star_inner
import Theorems.Thm_PI_UnitaryGroupMassFormula_PhSchurConv_Main_map_mul_apply
import Theorems.Thm_PI_UnitaryGroupMassFormula_PhSchurConv_Main_inner_map

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped InnerProductSpace
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.PhSchurConv PI.UnitaryGroupMassFormula.PhSchurConv.Main
open PI.PhSchurConv
namespace PI.UnitaryGroupMassFormula.PhSchurConv.Main
theorem _root_.solution {G : Type} [Group G] [TopologicalSpace G]
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : G → (H →L[ℂ] H)} (hU : IsURep σ) (g : G) (w : H) :
    ⟪w, σ g⁻¹ w⟫_ℂ = star ⟪w, σ g w⟫_ℂ := by
  rw [star_inner, ← inner_map hU g w (σ g⁻¹ w), ← map_mul_apply hU, mul_inv_cancel, hU.1,
    ContinuousLinearMap.one_apply]
end PI.UnitaryGroupMassFormula.PhSchurConv.Main
