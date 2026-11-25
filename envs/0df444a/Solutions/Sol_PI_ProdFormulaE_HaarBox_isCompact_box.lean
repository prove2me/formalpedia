-- Prove2me | solution 1 for PI.ProdFormulaE.HaarBox.isCompact_box
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:16:12.610603+00:00
-- url     : https://prove2.me/submissions/bf2bc3c6-fd30-4550-ba8a-f19371a3b0b9

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_HaarBox
import Theorems.Thm_PI_ProdFormulaE_HaarBox_isCompact_ball
import Theorems.Thm_PI_ProdFormulaE_HaarBox_box_eq_image

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
set_option linter.style.haveILetI false
open MeasureTheory Measure ValuativeRel Topology Filter Module
open scoped NNReal ENNReal Pointwise
open PI PI.ProdFormulaE PI.ProdFormulaE.HaarBox
variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {E : Type} [AddCommGroup E] [Module K E] [TopologicalSpace E] [IsModuleTopology K E]
variable {ι : Type} [Fintype ι] [DecidableEq ι]
namespace PI.ProdFormulaE.HaarBox
theorem _root_.solution (b : Basis ι K E) (γ : ι → ValueGroupWithZero K) : IsCompact (box b γ) := by
  rw [box_eq_image]
  exact (isCompact_univ_pi fun i => isCompact_ball (γ i)).image (continuous_equivFun_symm b)
end PI.ProdFormulaE.HaarBox
