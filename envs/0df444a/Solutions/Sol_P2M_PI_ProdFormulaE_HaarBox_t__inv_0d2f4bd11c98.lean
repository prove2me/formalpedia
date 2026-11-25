-- Prove2me | solution 1 for P2M_PI_ProdFormulaE_HaarBox_t__inv_0d2f4bd11c98
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:47:50.227685+00:00
-- url     : https://prove2.me/submissions/5abc8d59-6261-48d4-97cc-c695d122900f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_HaarBox
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_HaarTransv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ValuativeRel Module Matrix
open PI PI.ProdFormulaE PI.ProdFormulaE.HaarBox
variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {E : Type} [AddCommGroup E] [Module K E] [TopologicalSpace E] [IsModuleTopology K E]
variable {ι : Type} [Fintype ι] [DecidableEq ι]
namespace PI.ProdFormulaE.HaarBox
theorem _root_.solution (t : Matrix.TransvectionStruct ι K) : tγ t.inv = tγ t := by
  simp [tγ, Matrix.TransvectionStruct.inv, Valuation.map_neg]
end PI.ProdFormulaE.HaarBox
