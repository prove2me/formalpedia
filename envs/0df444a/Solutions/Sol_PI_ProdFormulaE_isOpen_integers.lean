-- Prove2me | solution 1 for PI.ProdFormulaE.isOpen_integers
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:40:11.005993+00:00
-- url     : https://prove2.me/submissions/d65f8ea1-2e9a-4b48-872d-d8af76090064

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_NormMod
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_NormIndex

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory ValuativeRel
open scoped Pointwise ENNReal NNReal
open PI PI.ProdFormulaE
variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [MeasurableSpace K] [BorelSpace K]
namespace PI.ProdFormulaE
theorem _root_.solution : IsOpen ((𝒪[K] : Subring K) : Set K) := by
  exact Valuation.isOpen_integer
end PI.ProdFormulaE
