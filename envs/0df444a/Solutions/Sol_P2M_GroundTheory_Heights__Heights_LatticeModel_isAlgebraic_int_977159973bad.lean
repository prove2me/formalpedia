-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LatticeModel_isAlgebraic_int_977159973bad
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:02:27.640358+00:00
-- url     : https://prove2.me/submissions/b92b9126-e52f-43dd-b1ae-cc15438724ed

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_POneBlockModelA

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
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G
noncomputable section
set_option linter.unusedSectionVars false
open GroundTheory.Heights₂.Heights.LatticeModel
variable {K : Type} [Field K] [NumberField K]
namespace GroundTheory.Heights₂.Heights.LatticeModel
theorem _root_.solution (x : K) : IsAlgebraic ℤ x :=
  IsFractionRing.isAlgebraic_iff ℤ ℚ K |>.mpr (.of_finite ℚ x)
end GroundTheory.Heights₂.Heights.LatticeModel
