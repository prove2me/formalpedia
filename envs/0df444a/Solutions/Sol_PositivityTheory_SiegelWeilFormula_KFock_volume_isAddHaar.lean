-- Prove2me | solution 1 for PositivityTheory.SiegelWeilFormula.KFock.volume_isAddHaar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:20:50.716649+00:00
-- url     : https://prove2.me/submissions/dbad854b-1d1d-4a1b-a272-0bfa72117e92

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_FockSpaces_VolumeIsAddHaar

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
open PositivityTheory PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.KFock
namespace PositivityTheory.SiegelWeilFormula.KFock
theorem _root_.solution (m n : ℕ) : (volume : Measure (Fin m → Fin n → ℂ)).IsAddHaarMeasure := by
  have h2 : (volume : Measure (Fin n → ℂ)).IsAddHaarMeasure := inferInstance
  have h3 : SigmaFinite (volume : Measure (Fin n → ℂ)) := inferInstance
  exact Measure.pi.isAddHaarMeasure _
end PositivityTheory.SiegelWeilFormula.KFock
