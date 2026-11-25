-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Regular_MollifiedLowerBound_closed_c81f5a75bc1d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:34:26.006284+00:00
-- url     : https://prove2.me/submissions/e9bc0fb2-e11a-40af-aa99-cdbd10465059

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_Statements
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshMoll
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PMollifierLowerBound
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_MollifiedLowerBound_proof_5068d8d26e40
import Theorems.Thm_ReciprocityTheory_AnForm_A_polyMaxLogConvex_thm
import Theorems.Thm_ReciprocityTheory_AnForm_A_subMeanPolydisc_thm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Regular
open MeasureTheory Metric Set
open ReciprocityTheory.AnForm.A
noncomputable section
namespace GroundTheory.Heights₂.Heights.Regular
namespace MollifiedLowerBound
theorem _root_.solution : MollifiedLowerBound.Statement :=
  MollifiedLowerBound.proof subMeanPolydisc_thm polyMaxLogConvex_thm
end MollifiedLowerBound
end GroundTheory.Heights₂.Heights.Regular
