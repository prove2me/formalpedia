-- Prove2me | solution 1 for PI.IsoDetW.Loc.map_mR_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:46:31.633936+00:00
-- url     : https://prove2.me/submissions/17f1ea15-09ad-4db5-96ce-8604e201f477

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDeterminant_LocalLat
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDeterminant_LocalDet
import Theorems.Thm_PI_IsoDetW_Loc_mR_apply

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
theorem _root_.solution (A : Submodule R (ι → K)) : A.map (mR (1 : Matrix ι ι K)) = A := by
  have : mR (R := R) (1 : Matrix ι ι K) = LinearMap.id := by
    refine LinearMap.ext fun x => ?_
    rw [LinearMap.id_apply, mR_apply, Matrix.one_mulVec]
  rw [this, Submodule.map_id]
end PI.IsoDetW.Loc
