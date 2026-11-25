-- Prove2me | solution 1 for PI.PhMeasCore.UnitaryGroupMassFormula.isClosed_UH
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:04:25.242592+00:00
-- url     : https://prove2.me/submissions/408c377b-decc-4dff-ac7a-7a80d31c357b

import Definitions.Def_Formalism_PeriodIntegrals_PhMeasCore
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SmoothTranslationMeasure_Development

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix Filter Topology
open scoped InnerProductSpace ContDiff
noncomputable section
open PI PI.PhMeasCore PI.PhMeasCore.UnitaryGroupMassFormula
open PI.PhMeasCore
namespace PI.PhMeasCore.UnitaryGroupMassFormula
theorem _root_.solution {n : ℕ} (Hm : Matrix (Fin n) (Fin n) ℂ) : IsClosed (UH Hm) := isClosed_eq ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul
  continuous_id) continuous_const
end PI.PhMeasCore.UnitaryGroupMassFormula
