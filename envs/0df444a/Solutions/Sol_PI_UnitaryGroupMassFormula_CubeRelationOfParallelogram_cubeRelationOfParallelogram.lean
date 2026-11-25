-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.CubeRelationOfParallelogram.cubeRelationOfParallelogram
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:19:33.880807+00:00
-- url     : https://prove2.me/submissions/b22e0788-722f-4afa-b571-cdd3e3534661

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_FglGram
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CubeFormalIdentities_CoeffPowMulPowEqZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CubeFormalIdentities_IsExpIntegralParallelogramOfNe
import Theorems.Thm_PI_UnitaryGroupMassFormula_CubeRelationOfParallelogram_constantCoeff_log_eq_zero
import Theorems.Thm_PI_UnitaryGroupMassFormula_CubeRelationOfParallelogram_isExpIntegral_parallelogram_of_ne
import Theorems.Thm_PI_UnitaryGroupMassFormula_CubeRelationOfParallelogram_good_sub
import Theorems.Thm_PI_UnitaryGroupMassFormula_CubeRelationOfParallelogram_simeq_iff_good


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Classical
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.CubeRelationOfParallelogram
open PI.FglGram MvPowerSeries
variable {p : ℕ} [Fact p.Prime] {σ τ : Type*}
namespace PI.UnitaryGroupMassFormula.CubeRelationOfParallelogram
theorem _root_.solution : CubeRelationOfParallelogram := by
  unfold PI.FglGram.CubeRelationOfParallelogram
  intro p _ l ex ph hlep hE1 hE3
  obtain ⟨hex, hX, -⟩ := hlep
  have hl := constantCoeff_log_eq_zero hex hX
  have product_zeroth_first_parts := isExpIntegral_parallelogram_of_ne ph hex hl 0 1 (by decide) hE1
  have sizeConstantAtParamsWeight := isExpIntegral_parallelogram_of_ne ph hex hl 1 2 (by decide) hE1
  have InnerProductFormulaField := isExpIntegral_parallelogram_of_ne ph hex hl 2 0 (by decide) hE1
  have H3 := (simeq_iff_good _ _).1 hE3
  rw [simeq_iff_good]
  have key := (good_sub ((good_sub ((good_sub H3) product_zeroth_first_parts)) sizeConstantAtParamsWeight)) InnerProductFormulaField
  convert key using 1
  ring
end PI.UnitaryGroupMassFormula.CubeRelationOfParallelogram
