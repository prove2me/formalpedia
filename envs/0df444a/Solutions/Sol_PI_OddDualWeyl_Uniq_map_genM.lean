-- Prove2me | solution 1 for PI.OddDualWeyl.Uniq.map_genM
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:24:40.603472+00:00
-- url     : https://prove2.me/submissions/c52e1a93-c020-4562-b74d-89199967ad92

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_JacRev
import Definitions.Def_Lemmata_GeneralBFactRightAlt_Imports
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_HighestWeightVectorUnique

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Matrix
noncomputable section
open PI PI.OddDualWeyl PI.OddDualWeyl.Uniq
variable {Rg : Type*} [CommRing Rg] {k : ℕ}
namespace PI.OddDualWeyl.Uniq
theorem _root_.solution : (dualSub Rg k).toRingHom.mapMatrix (genM Rg k) = dualM Rg k := by
  ext i j; simp [genM, dualSub]
end PI.OddDualWeyl.Uniq
