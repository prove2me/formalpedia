-- Prove2me | solution 1 for P2M_PI_ProdFormulaE_HaarBox_modF_nonneg__f21040a49df2
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:03:32.8712+00:00
-- url     : https://prove2.me/submissions/f53a098f-7e04-49b9-807e-03b5d1483f7f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_HaarBox
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_NormMod
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_ResCharIff
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_HaarMain
import Theorems.Thm_PI_ProdFormulaE_modF_pos
import Theorems.Thm_PI_ProdFormulaE_modF_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Measure ValuativeRel Topology Module
open scoped NNReal ENNReal Pointwise
open PI PI.ProdFormulaE PI.ProdFormulaE.HaarBox
variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
namespace PI.ProdFormulaE.HaarBox
theorem _root_.solution (a : K) : 0 ≤ modF K a := by
  rcases eq_or_ne a 0 with h | h
  · rw [h, modF_zero]
  · exact (modF_pos h).le
end PI.ProdFormulaE.HaarBox
