-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_ChartTorsion_incIdeal_le_ker_a605ce671589
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:29:26.079657+00:00
-- url     : https://prove2.me/submissions/1188aef7-9127-4161-a9b6-8bf07d8f22ca

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PChartTorsion
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_ChartTorsion_toChart_rename_90d568dd3801

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
open GroundTheory.Heights₂.Heights.Vertical.ChartTorsion
variable {D : Type} [CommRing D] {n : ℕ} (k : ℕ) (P : Ideal (MvPolynomial (Fin n) D)) (j : Fin n)
namespace GroundTheory.Heights₂.Heights.Vertical.ChartTorsion
theorem _root_.solution : incIdeal P k ≤ RingHom.ker (toChart k P j) := by
  refine sup_le (Ideal.map_le_iff_le_comap.2 fun p hp => ?_)
    (Ideal.span_le.2 (Set.range_subset_iff.2 fun i => ?_))
  · show toChart k P j (rename Sum.inl p) = 0
    rw [toChart_rename]
    simp [toBase, Ideal.Quotient.eq_zero_iff_mem.2 hp]
  · show toChart k P j _ = 0
    simp only [map_sum, map_mul]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
    have hs : ∀ l ∈ Finset.univ.erase j,
        toChart k P j (X (Sum.inr (i, l))) * toChart k P j (X (Sum.inl l)) =
          C (toBase P j (X l)) * X (i, l) := by
      intro l hl
      simp [toChart, solve, Finset.ne_of_mem_erase hl, mul_comm]
    rw [Finset.sum_congr rfl hs]
    have h1 : C (IsLocalization.Away.invSelf (Ideal.Quotient.mk P (X j))) * C (toBase P j (X j)) =
        (1 : MvPolynomial (Fin k × Fin n) (Base P j)) := by
      rw [← C_mul, mul_comm, toBase, RingHom.comp_apply, IsLocalization.Away.mul_invSelf, C_1]
    simp only [toChart, eval₂Hom_X', Sum.elim_inl, Sum.elim_inr, solve, ↓reduceIte]
    linear_combination (-(∑ l ∈ Finset.univ.erase j, C (toBase P j (X l)) * X (i, l))) * h1
end GroundTheory.Heights₂.Heights.Vertical.ChartTorsion
