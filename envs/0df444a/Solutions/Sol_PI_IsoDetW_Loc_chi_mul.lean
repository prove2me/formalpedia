-- Prove2me | solution 1 for PI.IsoDetW.Loc.chi_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:39:01.818625+00:00
-- url     : https://prove2.me/submissions/b6e5edd1-4615-43da-a719-8e8f4496349b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDeterminant_LocalLat
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDeterminant_LocalDet
import Theorems.Thm_PI_IsoDetW_Loc_lidx_mR
import Theorems.Thm_PI_IsoDetW_Loc_map_mR_mul
import Theorems.Thm_PI_IsoDetW_Loc_isLat_std
import Theorems.Thm_PI_IsoDetW_Loc_isLat_map
import Theorems.Thm_PI_IsoDetW_Loc_lat_cocycle


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
theorem _root_.solution (P : HeightOneSpectrum R) {g h : Matrix ι ι K} (hg : g.det ≠ 0) (hh : h.det ≠ 0) :
    chi R P (g * h) = chi R P g + chi R P h := by
  have hgh : (g * h).det ≠ 0 := by rw [Matrix.det_mul]; exact mul_ne_zero hg hh
  unfold chi
  rw [← map_mR_mul, lat_cocycle P (B := (std : Submodule R (ι → K)).map (mR g)) isLat_std
    (isLat_map g hg isLat_std) (isLat_map g hg (isLat_map h hh isLat_std)), lidx_mR P hg]
end PI.IsoDetW.Loc
