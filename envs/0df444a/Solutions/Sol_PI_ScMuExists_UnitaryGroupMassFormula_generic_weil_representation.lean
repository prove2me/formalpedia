-- Prove2me | solution 1 for PI.ScMuExists.UnitaryGroupMassFormula.generic_weil_representation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:06:42.933622+00:00
-- url     : https://prove2.me/submissions/def7420c-fed4-48f4-b600-f13125965c4a

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_InstDecomp
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_GenericWeilRepresentation
import Theorems.Thm_PI_ScMuExists_UnitaryGroupMassFormula_weil_of_bruhat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal Pointwise
noncomputable section
open PI PI.ScMuExists PI.ScMuExists.UnitaryGroupMassFormula
namespace PI.ScMuExists.UnitaryGroupMassFormula
theorem _root_.solution : GenWeil := by
  unfold GenWeil
  intro G _ _ _ _ _ _ _ _ μG μS _ _ _ S hS hSc hinv hpos hfin
  exact weil_of_bruhat μG μS S hS hSc hinv hpos hfin
end PI.ScMuExists.UnitaryGroupMassFormula
