-- Prove2me | solution 1 for PI.IsoDetW.Loc.std_map_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:43:31.345062+00:00
-- url     : https://prove2.me/submissions/71c25e58-6ea9-45a1-895b-db95df0585d5

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
theorem _root_.solution (D : ι → K) :
    (std : Submodule R (ι → K)).map (mR (Matrix.diagonal D)) =
      Submodule.pi Set.univ (fun i => ((FractionalIdeal.spanSingleton (nonZeroDivisors R) (D i) : FI) :
        Submodule R K)) := by
  ext x
  simp only [Submodule.mem_map, std, Submodule.mem_pi, Set.mem_univ, true_implies, Submodule.mem_one,
    FractionalIdeal.mem_coe, FractionalIdeal.mem_spanSingleton, mR_apply, Matrix.mulVec_diagonal]
  constructor
  · rintro ⟨y, hy, rfl⟩ i
    obtain ⟨w, hw⟩ := hy i
    exact ⟨w, by rw [Matrix.mulVec_diagonal, Algebra.smul_def, hw, mul_comm]⟩
  · intro h
    choose w hw using h
    refine ⟨fun i => algebraMap R K (w i), fun i => ⟨w i, rfl⟩, ?_⟩
    ext i
    rw [Matrix.mulVec_diagonal, ← hw i, Algebra.smul_def, mul_comm]
end PI.IsoDetW.Loc
