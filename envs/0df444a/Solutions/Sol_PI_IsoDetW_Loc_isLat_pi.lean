-- Prove2me | solution 1 for PI.IsoDetW.Loc.isLat_pi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:43:12.209587+00:00
-- url     : https://prove2.me/submissions/de837f9d-195e-4c3b-82cb-e5dc280c7151

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDeterminant_SpanSingletonAlgebraMap
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDeterminant_LocalPi
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDeterminant_LocalLat
import Theorems.Thm_PI_IsoDetW_Loc_span_le_span
import Theorems.Thm_P2M_PI_IsoDetW_Loc_algebraMap_ne_zero__6cbe823fda71
import Theorems.Thm_PI_IsoDetW_Loc_exists_sandwich


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
omit [DecidableEq ι]
namespace PI.IsoDetW.Loc
theorem _root_.solution (c : ι → FI) (hc : ∀ i, c i ≠ 0) :
    IsLat (Submodule.pi Set.univ (fun i => (c i : Submodule R K))) := by
  classical
  choose r hr hr1 hr2 using fun i => exists_sandwich (c i) (hc i)
  have hP : ∀ i, (∏ j ∈ Finset.univ.erase i, r j) ≠ 0 :=
    fun i => Finset.prod_ne_zero_iff.2 fun j _ => hr j
  refine ⟨∏ i, r i, Finset.prod_ne_zero_iff.2 fun i _ => hr i, ?_, ?_⟩
  · refine Submodule.pi_mono fun i _ => ?_
    refine FractionalIdeal.coe_le_coe.2 ((span_le_span (∏ j ∈ Finset.univ.erase i, r j) ?_).trans (hr1 i))
    rw [← map_mul, Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
  · refine Submodule.pi_mono fun i _ => ?_
    refine FractionalIdeal.coe_le_coe.2 ((hr2 i).trans (span_le_span (∏ j ∈ Finset.univ.erase i, r j) ?_))
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i), map_mul, mul_inv, ← mul_assoc,
      mul_inv_cancel₀ (algebraMap_ne_zero' (hP i)), one_mul]
end PI.IsoDetW.Loc
