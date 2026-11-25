-- Prove2me | solution 1 for PI.ProdFormulaE.isCompact_integers
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:06:10.648943+00:00
-- url     : https://prove2.me/submissions/29db9f8c-0df7-4e35-af70-94de60475c58

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
theorem _root_.solution : IsCompact ((𝒪[K] : Subring K) : Set K) := by
  exact isCompact_iff_compactSpace.mpr (inferInstanceAs (CompactSpace 𝒪[K]))
end PI.ProdFormulaE
