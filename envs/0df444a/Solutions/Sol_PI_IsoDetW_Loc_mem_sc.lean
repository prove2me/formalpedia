-- Prove2me | solution 1 for PI.IsoDetW.Loc.mem_sc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:46:41.113196+00:00
-- url     : https://prove2.me/submissions/7335ba24-b087-48d6-9cd6-2357130ec9e5

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
omit [IsDedekindDomain R] [DecidableEq ι]
namespace PI.IsoDetW.Loc
theorem _root_.solution {a : K} {v : ι → K} :
    v ∈ (sc a : Submodule R (ι → K)) ↔ ∀ i, ∃ z : R, z • a = v i := by
  simp [sc, Submodule.mem_pi, Submodule.mem_span_singleton]
end PI.IsoDetW.Loc
