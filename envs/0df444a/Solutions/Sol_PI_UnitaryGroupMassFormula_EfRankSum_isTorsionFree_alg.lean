-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.EfRankSum.isTorsionFree_alg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:46:25.160821+00:00
-- url     : https://prove2.me/submissions/569aeab5-b4b7-47d3-b888-75bce4f6ca52

import Definitions.Def_Formalism_PeriodIntegrals_EfRankSum
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RamificationRankSum_Lattice

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.EfRankSum
open Formalism.MainNotions.Gaps.EtaleWeightGaps
namespace PI.UnitaryGroupMassFormula.EfRankSum
theorem _root_.solution (O : Type) [CommRing O] [IsDomain O]
    (K : Type) [Field K] [Algebra O K] [IsFractionRing O K]
    (A : Type) [CommRing A] [Algebra O A] [Algebra K A] [IsScalarTower O K A] :
    Module.IsTorsionFree O A := by
  refine ⟨fun r hr a b hab => ?_⟩
  have hab' : r • a = r • b := hab
  have hr0 : r ≠ 0 := hr.ne_zero
  have hK : algebraMap O K r ≠ 0 := by
    simpa using (IsFractionRing.injective O K).ne hr0
  have h1 : (algebraMap O K r) • a = (algebraMap O K r) • b := by
    rw [algebraMap_smul, algebraMap_smul]
    exact hab'
  calc a = ((algebraMap O K r)⁻¹ * algebraMap O K r) • a := by rw [inv_mul_cancel₀ hK, one_smul]
    _ = ((algebraMap O K r)⁻¹ * algebraMap O K r) • b := by rw [mul_smul, h1, ← mul_smul]
    _ = b := by rw [inv_mul_cancel₀ hK, one_smul]
end PI.UnitaryGroupMassFormula.EfRankSum
