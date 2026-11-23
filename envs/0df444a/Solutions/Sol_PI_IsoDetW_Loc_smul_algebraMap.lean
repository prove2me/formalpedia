-- Prove2me | solution 1 for PI.IsoDetW.Loc.smul_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:31:12.232599+00:00
-- url     : https://prove2.me/submissions/3f9eb2de-2f4a-454e-a0ee-9d1f60adb73b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDeterminant_LidxAntisymm
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDeterminant_AlgebraMapMemCI

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.IsoDetW PI.IsoDetW.Loc
open PI.IsoDetDefs IsDedekindDomain
variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
namespace PI.IsoDetW.Loc
theorem _root_.solution (s y : R) : s • algebraMap R K y = algebraMap R K (s * y) := by
  rw [Algebra.smul_def, map_mul]
end PI.IsoDetW.Loc
