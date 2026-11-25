-- Prove2me | solution 1 for PI.IsoDetW.Loc.lidx_mR
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:55:07.561406+00:00
-- url     : https://prove2.me/submissions/39a5ef82-9f58-4094-a4c8-5940a0de15db

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDeterminant_LocalLat
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDeterminant_LocalDet
import Theorems.Thm_PI_IsoDetW_Loc_mR_injective
import Theorems.Thm_PI_IsoDetW_Loc_mR_sat
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
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
local notation "FI" => FractionalIdeal (nonZeroDivisors R) K
namespace PI.IsoDetW.Loc
theorem _root_.solution (P : HeightOneSpectrum R) {g : Matrix ι ι K} (hg : g.det ≠ 0)
    (A B : Submodule R (ι → K)) :
    lidx P.asIdeal (A.map (mR g)) (B.map (mR g)) = lidx P.asIdeal A B :=
  lidx_map P.asIdeal (mR g) (mR_injective hg) (mR_sat P g) A B
end PI.IsoDetW.Loc
