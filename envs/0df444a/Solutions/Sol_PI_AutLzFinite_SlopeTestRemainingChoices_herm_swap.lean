-- Prove2me | solution 1 for PI.AutLzFinite.SlopeTestRemainingChoices.herm_swap
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:04:12.293808+00:00
-- url     : https://prove2.me/submissions/545789e3-1196-4b69-a521-36deffbeac32

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataSpaces
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismFiniteness_SylvesterLe
import Definitions.Def_Lemmata_GeneralBFactUpperAltForm_Imports
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismFiniteness_MulVecMapInjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.AutLzFinite PI.AutLzFinite.SlopeTestRemainingChoices
open Matrix Formalism.BasicNotions
variable {E : Type} [Field E] [NumberField E] [StarRing E] (S : HSpace E)
namespace PI.AutLzFinite.SlopeTestRemainingChoices
theorem _root_.solution (x y : S.V) : S.hT y x = star (S.hT x y) := by
  rw [← S.herm.eq x y]; rfl
end PI.AutLzFinite.SlopeTestRemainingChoices
