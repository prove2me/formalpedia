-- Prove2me | solution 1 for PI.ProdFormulaE.HaarBox.isCompact_ball
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:11:26.714799+00:00
-- url     : https://prove2.me/submissions/503f8176-82d4-4ed5-b165-c8f8c511c465

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_HaarBox

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
variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {K}
namespace PI.ProdFormulaE.HaarBox
theorem _root_.solution (γ : ValueGroupWithZero K) : IsCompact {x : K | valuation K x ≤ γ} :=
  IsNonarchimedeanLocalField.isCompact_closedBall K γ
end PI.ProdFormulaE.HaarBox
