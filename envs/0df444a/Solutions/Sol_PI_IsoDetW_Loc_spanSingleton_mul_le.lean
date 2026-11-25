-- Prove2me | solution 1 for PI.IsoDetW.Loc.spanSingleton_mul_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:43:29.7808+00:00
-- url     : https://prove2.me/submissions/b6104fa9-2370-4652-9395-8ec589682063

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDeterminant_AlgebraMapMemCI
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDeterminant_SpanSingletonAlgebraMap

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
local notation "FI" => FractionalIdeal (nonZeroDivisors R) K
namespace PI.IsoDetW.Loc
theorem _root_.solution (x y : R) :
    FractionalIdeal.spanSingleton (nonZeroDivisors R) (algebraMap R K (x * y)) ≤
      FractionalIdeal.spanSingleton (nonZeroDivisors R) (algebraMap R K x) := by
  rw [FractionalIdeal.spanSingleton_le_iff_mem, FractionalIdeal.mem_spanSingleton]
  exact ⟨y, by rw [Algebra.smul_def, map_mul, mul_comm]⟩
end PI.IsoDetW.Loc
