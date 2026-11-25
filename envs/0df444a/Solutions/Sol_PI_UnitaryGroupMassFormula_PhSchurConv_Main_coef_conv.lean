-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.PhSchurConv.Main.coef_conv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:44:50.544498+00:00
-- url     : https://prove2.me/submissions/d0221e78-b440-4743-a52f-a5a2c01925f2

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_PhSchurConv
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SchurConvolution_MapMulApply
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
    {σ : G → (H →L[ℂ] H)} (hU : IsURep σ) (g x y : G) (w : H) :
    ⟪w, σ (x⁻¹ * g⁻¹ * y) w⟫_ℂ = ⟪σ g (σ x w), σ y w⟫_ℂ := by
  have h1 : σ g (σ x w) = σ (g * x) w := (map_mul_apply hU g x w).symm
  rw [h1]
  symm
  calc ⟪σ (g * x) w, σ y w⟫_ℂ = ⟪σ (g * x)⁻¹ (σ (g * x) w), σ (g * x)⁻¹ (σ y w)⟫_ℂ := (inner_map hU _ _ _).symm
    _ = ⟪w, σ (x⁻¹ * g⁻¹ * y) w⟫_ℂ := by
      rw [← map_mul_apply hU, ← map_mul_apply hU, inv_mul_cancel, hU.1, ContinuousLinearMap.one_apply,
        mul_inv_rev]
end PI.UnitaryGroupMassFormula.PhSchurConv.Main
