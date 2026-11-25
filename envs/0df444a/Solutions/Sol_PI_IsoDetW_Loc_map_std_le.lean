-- Prove2me | solution 1 for PI.IsoDetW.Loc.map_std_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:46:35.074483+00:00
-- url     : https://prove2.me/submissions/6f8c4565-c6e3-4eec-b94e-8028a21ecc8e

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
theorem _root_.solution {g : Matrix ι ι K} (hg : ∀ a b, ∃ z : R, algebraMap R K z = g a b) :
    (std : Submodule R (ι → K)).map (mR g) ≤ std := by
  rintro _ ⟨y, hy, rfl⟩
  have hy' : ∀ b, ∃ w : R, algebraMap R K w = y b := fun b =>
    Submodule.mem_one.mp ((Submodule.mem_pi.mp hy) b (Set.mem_univ b))
  choose w hw using hy'
  choose z hz using hg
  refine Submodule.mem_pi.mpr (fun a _ => Submodule.mem_one.mpr ?_)
  refine ⟨∑ b, z a b * w b, ?_⟩
  rw [mR_apply, Matrix.mulVec, dotProduct, map_sum]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [map_mul, hz, hw]
end PI.IsoDetW.Loc
