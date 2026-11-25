-- Prove2me | solution 1 for PI.IsoDetW.Loc.lidx_mulR
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:00:02.912004+00:00
-- url     : https://prove2.me/submissions/a36fa7e8-5035-4ab8-b0ff-959640b9373e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDeterminant_AlgebraMapMemCI
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDeterminant_SpanSingletonAlgebraMap
import Theorems.Thm_PI_IsoDetW_Loc_mulR_injective
import Theorems.Thm_PI_IsoDetW_Loc_mulR_sat
import Theorems.Thm_PI_IsoDetW_Loc_map_mulR
import Theorems.Thm_PI_IsoDetW_Loc_lidx_map


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
theorem _root_.solution (P : HeightOneSpectrum R) {a : K} (ha : a ≠ 0) (I J : FI) :
    lidx P.asIdeal ((FractionalIdeal.spanSingleton _ a * I : FI) : Submodule R K)
      ((FractionalIdeal.spanSingleton _ a * J : FI) : Submodule R K) =
    lidx P.asIdeal (I : Submodule R K) (J : Submodule R K) := by
  rw [← map_mulR, ← map_mulR]
  exact lidx_map P.asIdeal (mulR a) (mulR_injective ha) (mulR_sat P.asIdeal a) _ _
end PI.IsoDetW.Loc
