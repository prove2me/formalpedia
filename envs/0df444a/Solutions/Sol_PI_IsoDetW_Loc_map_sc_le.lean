-- Prove2me | solution 1 for PI.IsoDetW.Loc.map_sc_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:54:01.617895+00:00
-- url     : https://prove2.me/submissions/71ec67e7-cf40-4ee5-9929-d7ba59774e18

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDeterminant_SpanSingletonAlgebraMap
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDeterminant_LocalPi
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDeterminant_LocalLat
import Theorems.Thm_PI_IsoDetW_Loc_mem_sc
import Theorems.Thm_P2M_PI_IsoDetW_Loc_algebraMap_ne_zero__6cbe823fda71

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
  {ι : Type*} [Fintype ι] [DecidableEq ι]
local notation "FI" => FractionalIdeal (nonZeroDivisors R) K
omit [IsDedekindDomain R]
namespace PI.IsoDetW.Loc
theorem _root_.solution (M : Matrix ι ι K) {d : R} (hd0 : d ≠ 0)
    (hd : ∀ i j, IsLocalization.IsInteger R (d • M i j)) (a : K) :
    (sc a : Submodule R (ι → K)).map (M.mulVecLin.restrictScalars R) ≤ sc (a * (algebraMap R K d)⁻¹) := by
  rintro _ ⟨v, hv, rfl⟩
  rw [SetLike.mem_coe, mem_sc] at hv
  rw [mem_sc]
  choose z hz using hv
  choose m hm using hd
  have had := algebraMap_ne_zero' (K := K) hd0
  intro k
  refine ⟨∑ j, m k j * z j, ?_⟩
  simp only [LinearMap.coe_restrictScalars, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct]
  rw [Algebra.smul_def, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← hz j, map_mul, hm k j, Algebra.smul_def, Algebra.smul_def]
  field_simp
end PI.IsoDetW.Loc
