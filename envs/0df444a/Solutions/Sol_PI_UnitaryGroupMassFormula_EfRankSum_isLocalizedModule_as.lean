-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.EfRankSum.isLocalizedModule_as
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:40:22.595612+00:00
-- url     : https://prove2.me/submissions/69bbeb5a-341c-4396-a683-1e654c3e7dec

import Definitions.Def_Formalism_PeriodIntegrals_EfRankSum
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RamificationRankSum_Lattice
import Theorems.Thm_PI_UnitaryGroupMassFormula_EfRankSum_isTorsionFree_alg

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
theorem _root_.solution (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (K : Type) [Field K] [Algebra O K] [IsFractionRing O K]
    (A : Type) [CommRing A] [Algebra O A] [Algebra K A] [IsScalarTower O K A] [FiniteDimensional K A] :
    IsLocalizedModule (nonZeroDivisors O) ((As O A).val.toLinearMap) := by
  obtain ⟨htf⟩ := isTorsionFree_alg O K A
  refine IsLocalizedModule.mk ?_ ?_ ?_
  · intro s
    have hs : algebraMap O K s ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors s.2
    rw [Module.End.isUnit_iff]
    refine ⟨?_, ?_⟩
    · intro x y hxy
      simp only [Module.algebraMap_end_apply] at hxy
      exact htf (isRegular_of_ne_zero (nonZeroDivisors.ne_zero s.2)) hxy
    · intro y
      refine ⟨(algebraMap O K s)⁻¹ • y, ?_⟩
      simp only [Module.algebraMap_end_apply]
      rw [← algebraMap_smul K (s : O), smul_smul, mul_inv_cancel₀ hs, one_smul]
  · intro y
    have hy : IsAlgebraic K y := Algebra.IsAlgebraic.isAlgebraic y
    have hyO : IsAlgebraic O y := (IsFractionRing.isAlgebraic_iff O K A).mpr hy
    obtain ⟨c, hc0, hc⟩ := hyO.exists_integral_multiple
    refine ⟨(⟨c • y, hc⟩, ⟨c, mem_nonZeroDivisors_of_ne_zero hc0⟩), ?_⟩
    rfl
  · intro x₁ x₂ h
    exact ⟨1, by rw [Subtype.ext h]⟩
end PI.UnitaryGroupMassFormula.EfRankSum
