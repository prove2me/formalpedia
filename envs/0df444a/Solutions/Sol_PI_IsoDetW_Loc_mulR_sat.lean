-- Prove2me | solution 1 for PI.IsoDetW.Loc.mulR_sat
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:37:01.169804+00:00
-- url     : https://prove2.me/submissions/a5bf88bd-1548-43f0-8603-03ee59dd6a7b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDeterminant_AlgebraMapMemCI
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDeterminant_SpanSingletonAlgebraMap
import Theorems.Thm_PI_IsoDetW_Loc_sat_of_linear


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
theorem _root_.solution (p : Ideal R) [p.IsPrime] (a : K) (s : R) (y : K) (hs : s ∈ p.primeCompl)
    (hy : s • y ∈ LinearMap.range (mulR (R := R) a)) : y ∈ LinearMap.range (mulR (R := R) a) :=
  sat_of_linear p (LinearMap.mulLeft K a) s y hs hy
end PI.IsoDetW.Loc
