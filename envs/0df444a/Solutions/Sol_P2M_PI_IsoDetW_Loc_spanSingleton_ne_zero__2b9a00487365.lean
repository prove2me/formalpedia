-- Prove2me | solution 1 for P2M_PI_IsoDetW_Loc_spanSingleton_ne_zero__2b9a00487365
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:13:26.819381+00:00
-- url     : https://prove2.me/submissions/8d367806-e871-4773-8042-950fd4bb7fcf

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDeterminant_SpanSingletonAlgebraMap
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDeterminant_LocalPi
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDeterminant_LocalLat

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
  {ι : Type*} [Fintype ι] [DecidableEq ι]
local notation "FI" => FractionalIdeal (nonZeroDivisors R) K
omit [IsDedekindDomain R]
namespace PI.IsoDetW.Loc
theorem _root_.solution {a : K} (ha : a ≠ 0) :
    FractionalIdeal.spanSingleton (nonZeroDivisors R) a ≠ 0 := by
  rw [ne_eq, FractionalIdeal.spanSingleton_eq_zero_iff]; exact ha
end PI.IsoDetW.Loc
