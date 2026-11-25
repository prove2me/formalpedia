-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_eq_of_sum_eq_nsmul_of_norm_le_831fa282c107
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:27:53.905996+00:00
-- url     : https://prove2.me/submissions/b3c5c24e-a2f5-4848-967f-1c1063c89a1f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalMaximumPrinciple
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLocalTrace
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PNormalMaximumPrinciple

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open MvPolynomial Topology Filter RealInnerProductSpace
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
theorem _root_.solution {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {m : ℕ}
    (a : Fin m → E) (c : E) (hle : ∀ j, ‖a j‖ ≤ ‖c‖) (hsum : ∑ j, a j = m • c) (j : Fin m) :
    a j = c := by
  have hj : ∀ i, ⟪c, a i⟫ ≤ ‖c‖ ^ 2 := fun i =>
    (real_inner_le_norm c (a i)).trans
      (by rw [sq]; exact mul_le_mul_of_nonneg_left (hle i) (norm_nonneg c))
  have htot : ∑ i, ⟪c, a i⟫ = m * ‖c‖ ^ 2 := by
    rw [← inner_sum, hsum, ← Nat.cast_smul_eq_nsmul ℝ, real_inner_smul_right,
      real_inner_self_eq_norm_sq]
  have h0 := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sub_nonneg.2 (hj i))).1
    (by rw [Finset.sum_sub_distrib, htot, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, sub_self]) j (Finset.mem_univ j)
  have hsq : ‖a j - c‖ ^ 2 ≤ 0 := by
    rw [norm_sub_sq_real, real_inner_comm]
    nlinarith [hle j, norm_nonneg (a j), norm_nonneg c]
  exact sub_eq_zero.1 (norm_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1
    (le_antisymm hsq (sq_nonneg _))))
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
