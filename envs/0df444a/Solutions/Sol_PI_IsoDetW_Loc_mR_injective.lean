-- Prove2me | solution 1 for PI.IsoDetW.Loc.mR_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:46:14.68988+00:00
-- url     : https://prove2.me/submissions/90255b81-bb1f-4872-8b18-a051d5f7dd41

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
theorem _root_.solution {g : Matrix ι ι K} (hg : g.det ≠ 0) : Function.Injective (mR (R := R) g) := by
  intro x y h
  have h2 := congrArg (fun v => g⁻¹.mulVec v) h
  simp only [mR_apply, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (Ne.isUnit hg),
    Matrix.one_mulVec] at h2
  exact h2
end PI.IsoDetW.Loc
