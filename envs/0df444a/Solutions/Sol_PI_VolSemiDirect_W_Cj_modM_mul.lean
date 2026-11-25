-- Prove2me | solution 1 for PI.VolSemiDirect.W.Cj.modM_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:00:05.444518+00:00
-- url     : https://prove2.me/submissions/a3efe239-23d5-4456-9889-3d13545b607b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_CjDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_TopoAFTop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_MapPhiOfModM
import Theorems.Thm_PI_VolSemiDirect_W_Cj_phi_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolSemiDirect PI.VolSemiDirect.W PI.VolSemiDirect.W.Cj
open MeasureTheory Measure
open scoped NNReal
variable {A : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [LocallyCompactSpace A] [SecondCountableTopology A] [T2Space A] [MeasurableSpace A]
  [BorelSpace A] {k : ℕ}
namespace PI.VolSemiDirect.W.Cj
theorem _root_.solution (X Y : GL (Fin k) A) : modM (X * Y) = modM X * modM Y := by
  simp only [modM, phi_mul, addEquivAddHaarChar_trans, mul_comm]
end PI.VolSemiDirect.W.Cj
