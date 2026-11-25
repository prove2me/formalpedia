-- Prove2me | solution 1 for PI.IsoDetW.Loc.map_std_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:54:31.225818+00:00
-- url     : https://prove2.me/submissions/4657dd1d-ab3f-4ddc-bff2-9f6ee1c4b0ff

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDeterminant_LocalLat
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDeterminant_LocalDet
import Theorems.Thm_PI_IsoDetW_Loc_mR_apply
import Theorems.Thm_PI_IsoDetW_Loc_map_std_le

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
theorem _root_.solution {g g' : Matrix ι ι K} (hg : ∀ a b, ∃ z : R, algebraMap R K z = g a b)
    (hg' : ∀ a b, ∃ z : R, algebraMap R K z = g' a b) (hgg' : g * g' = 1) :
    (std : Submodule R (ι → K)).map (mR g) = std := by
  refine le_antisymm (map_std_le hg) (fun y hy => ?_)
  refine ⟨g'.mulVec y, map_std_le hg' ⟨y, hy, rfl⟩, ?_⟩
  simp [mR_apply, Matrix.mulVec_mulVec, hgg']
end PI.IsoDetW.Loc
