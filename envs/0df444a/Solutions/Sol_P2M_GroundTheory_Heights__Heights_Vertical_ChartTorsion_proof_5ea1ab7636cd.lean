-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_ChartTorsion_proof_5ea1ab7636cd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:54:09.079985+00:00
-- url     : https://prove2.me/submissions/ac45f93c-1422-49de-a3aa-30a7fdfca7e0

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PChartTorsion
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_ChartTorsion_incIdeal_le_ker_a605ce671589
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_ChartTorsion_back_toChart_ecd1711253b1

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Vertical
open MvPolynomial
noncomputable section
open ChartTorsion
namespace GroundTheory.Heights₂.Heights.Vertical
namespace ChartTorsion
theorem _root_.solution : ChartTorsion.Statement := by
  intro D _ _ n k P hP hPD c g hc hcg j
  by_cases hj : (X j : MvPolynomial (Fin n) D) ∈ P
  · refine ⟨1, Ideal.mul_mem_right _ _ (Ideal.mem_sup_left ?_)⟩
    simpa using Ideal.mem_map_of_mem (rename (R := D) (Sum.inl (β := Fin k × Fin n))) hj
  have hx : Ideal.Quotient.mk P (X j) ≠ 0 := fun h => hj (Ideal.Quotient.eq_zero_iff_mem.1 h)
  have hle : Submonoid.powers (Ideal.Quotient.mk P (X j)) ≤ nonZeroDivisors _ :=
    powers_le_nonZeroDivisors_of_noZeroDivisors hx
  have : IsDomain (Base P j) := IsLocalization.isDomain_localization hle
  have hcz : toChart k P j (C c) ≠ 0 := by
    simp only [toChart, eval₂Hom_C, RingHom.comp_apply, ne_eq, C_eq_zero, toBase]
    rw [map_eq_zero_iff _ (IsLocalization.injective (Base P j) hle)]
    intro h
    exact hc (hPD c (Ideal.Quotient.eq_zero_iff_mem.1 h))
  have hg0 : toChart k P j g = 0 := by
    have h := incIdeal_le_ker k P j hcg
    rw [RingHom.mem_ker, map_mul] at h
    exact (mul_eq_zero.1 h).resolve_left hcz
  have hl : toLoc k P j g = 0 := by
    rw [← back_toChart, hg0, map_zero]
  obtain ⟨⟨_, N, rfl⟩, hN⟩ := (IsLocalization.map_eq_zero_iff
    (Submonoid.powers (Ideal.Quotient.mk (incIdeal P k) (X (Sum.inl j)))) _ _).1 hl
  refine ⟨N, Ideal.Quotient.eq_zero_iff_mem.1 ?_⟩
  simpa [map_mul, map_pow] using hN
end ChartTorsion
end GroundTheory.Heights₂.Heights.Vertical
