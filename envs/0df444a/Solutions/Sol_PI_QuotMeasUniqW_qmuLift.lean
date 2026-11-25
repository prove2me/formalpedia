-- Prove2me | solution 1 for PI.QuotMeasUniqW.qmuLift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:42:10.431733+00:00
-- url     : https://prove2.me/submissions/b9df0238-0145-4b0e-b894-a3a67292b235

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuotientMeasureUniqueness_QmuWeight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuotientMeasureUniqueness_QLiftIsMulLeftInvariant
import Theorems.Thm_PI_QuotMeasUniqW_lintegral_qLift
import Theorems.Thm_PI_QuotMeasUniqW_qLift_isMulLeftInvariant
import Theorems.Thm_PI_QuotMeasUniqW_qLift_finite

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Pointwise
open scoped ENNReal
open PI PI.QuotMeasUniqW
namespace PI.QuotMeasUniqW
theorem _root_.solution : QmuLift := by
  intro G _ _ _ _ _ _ _ _ H hH ν hν ρ hρK hρg
  have : LocallyCompactSpace H := hH.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have : SecondCountableTopology H := TopologicalSpace.Subtype.secondCountableTopology (H : Set G)
  have : SigmaCompactSpace H := inferInstance
  have : SigmaFinite ν := inferInstance
  exact ⟨qLift ν ρ, qLift_isMulLeftInvariant ν ρ hρg,
    qLift_finite hH ν ρ hρK, fun f hf => lintegral_qLift ν ρ hf⟩
end PI.QuotMeasUniqW
