-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_sheetJac_nonneg_cd90e2bb5cf3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:46:36.984607+00:00
-- url     : https://prove2.me/submissions/a5e4c857-c270-4a42-a96b-e2c2b279b7d7

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsCurrent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StAreaMultiplicity
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSheetComass

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory Matrix ComplexSets
noncomputable section
variable {n d : ℕ}
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (s : (Fin d → ℂ) → Fin n → ℂ) (y : Fin d → ℂ) : 0 ≤ sheetJac s y :=
  Real.sqrt_nonneg _
end GroundTheory.Heights₂.Heights
