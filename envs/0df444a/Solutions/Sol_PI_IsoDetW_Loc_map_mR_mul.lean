-- Prove2me | solution 1 for PI.IsoDetW.Loc.map_mR_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:00:23.263891+00:00
-- url     : https://prove2.me/submissions/ceb962e0-49db-4a10-aa78-dd581e85459b

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
theorem _root_.solution (g h : Matrix ι ι K) (A : Submodule R (ι → K)) :
    (A.map (mR h)).map (mR g) = A.map (mR (g * h)) := by
  rw [← Submodule.map_comp]
  congr 1
  refine LinearMap.ext fun x => ?_
  rw [LinearMap.comp_apply, mR_apply, mR_apply, mR_apply, Matrix.mulVec_mulVec]
end PI.IsoDetW.Loc
