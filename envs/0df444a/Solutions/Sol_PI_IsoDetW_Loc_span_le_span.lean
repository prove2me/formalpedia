-- Prove2me | solution 1 for PI.IsoDetW.Loc.span_le_span
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:38:10.648857+00:00
-- url     : https://prove2.me/submissions/43786ad9-57ca-402c-8bd1-0ac4aed09c28

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
theorem _root_.solution {a b : K} (t : R) (h : a = algebraMap R K t * b) :
    FractionalIdeal.spanSingleton (nonZeroDivisors R) a ≤ FractionalIdeal.spanSingleton (nonZeroDivisors R) b := by
  rw [FractionalIdeal.spanSingleton_le_iff_mem, FractionalIdeal.mem_spanSingleton]
  exact ⟨t, by rw [Algebra.smul_def, h]⟩
end PI.IsoDetW.Loc
