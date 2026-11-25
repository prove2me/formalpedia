-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_UnitsInvHaar_measurable_units_val_52add3eb92ee
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:54:24.246797+00:00
-- url     : https://prove2.me/submissions/0d8e2331-3ea6-4010-971b-bb3954f2b275

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsUnitsInvHaar
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PUnitsInvHaar

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open MeasureTheory Measure Set
open scoped ENNReal NNReal
noncomputable section
open GroundTheory.Heights₂.Heights.FiniteCovolume.UnitsInvHaar
variable {I : Type*} [Fintype I]
namespace GroundTheory.Heights₂.Heights.FiniteCovolume.UnitsInvHaar
theorem _root_.solution : Measurable (Units.val : ℂˣ → ℂ) := fun _ hs => ⟨_, hs, rfl⟩
end GroundTheory.Heights₂.Heights.FiniteCovolume.UnitsInvHaar
