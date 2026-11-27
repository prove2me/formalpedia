-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartDenominatorAlt_proof_5da06b6208a9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:53:25.181626+00:00
-- url     : https://prove2.me/submissions/5de607e5-7d0e-4aaf-af31-dc9ba350a20f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_MemPointsOfGeneratorsVanish
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_contDiff_evalCone_423dd9a0547d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ContDiffOn_zpow_of_ne_zero_5e8a446e8168
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ArithVariety_mem_points_of_generators_vanish_912fad86b1ee
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_evalCone_chartMonomial_fd0871b69c38


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
open scoped ContDiff
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
namespace GroundTheory.Heights₂.Heights
namespace ChartDenominatorAlt
theorem _root_.solution (hV : ChartVanishing.Statement) : ChartDenominatorAlt.Statement := by
  intro ι _ _ n P D d g hg r G δ hG
  refine ⟨fun z hz ↦ ?_, ?_⟩
  · have hB : 0 ≤ ∑ i, ‖evalCone z (G i)‖ ^ 2 *
        ∏ k, l2Norm (z k) ^ (2 * ((d k : ℤ) + D.deg k - δ i k)) :=
      Finset.sum_nonneg fun i _ ↦ mul_nonneg (sq_nonneg _)
        (Finset.prod_nonneg fun k _ ↦ zpow_nonneg (Real.sqrt_nonneg _) _)
    have hA : 0 ≤ ∑ c, ∑ j, ‖evalCone z (g c j)‖ ^ 2 :=
      Finset.sum_nonneg fun c _ ↦ Finset.sum_nonneg fun j _ ↦ sq_nonneg _
    unfold AddBlockData.den
    by_cases hGz : ∃ i, evalCone z (G i) ≠ 0
    · obtain ⟨i, hi⟩ := hGz
      refine add_pos_of_nonneg_of_pos hA (Finset.sum_pos' (fun i _ ↦ ?_) ⟨i, Finset.mem_univ i, ?_⟩)
      · exact mul_nonneg (sq_nonneg _)
          (Finset.prod_nonneg fun k _ ↦ zpow_nonneg (Real.sqrt_nonneg _) _)
      · exact mul_pos (pow_pos (norm_pos_iff.mpr hi) 2)
          (Finset.prod_pos fun k _ ↦ zpow_pos (vectorL2Norm_pos (hz k)) _)
    · push Not at hGz
      have hzP := P.mem_points_of_generators_vanish hG hz hGz
      have hc : ∀ k, ∃ i, z k i ≠ 0 := fun k ↦ Function.ne_iff.mp (hz k)
      choose c hc using hc
      have hm : evalCone z (chartMonomial c d) ≠ 0 := by
        rw [evalCone_chartMonomial]
        exact Finset.prod_ne_zero_iff.mpr fun k _ ↦ pow_ne_zero _ (hc k)
      have hj : ∃ j, evalCone z (g c j) ≠ 0 := by
        by_contra hne
        push Not at hne
        exact hm ((hV ι n P D d g hg z hzP c).mp hne)
      obtain ⟨j, hj⟩ := hj
      refine add_pos_of_pos_of_nonneg (Finset.sum_pos' (fun c _ ↦ ?_) ⟨c, Finset.mem_univ c, ?_⟩) hB
      · exact Finset.sum_nonneg fun j _ ↦ sq_nonneg _
      · exact Finset.sum_pos' (fun j _ ↦ sq_nonneg _)
          ⟨j, Finset.mem_univ j, pow_pos (norm_pos_iff.mpr hj) 2⟩
  · have hsq : ∀ f : MvPolynomial (Coord n) ℤ,
        ContDiff ℝ ∞ (fun z : Cone n ℂ ↦ ‖evalCone z f‖ ^ 2) :=
      fun f ↦ (contDiff_norm_sq ℝ).comp (contDiff_evalCone f)
    unfold AddBlockData.den
    refine ContDiffOn.add ?_ ?_
    · exact (ContDiff.sum fun c _ ↦ ContDiff.sum fun j _ ↦ hsq (g c j)).contDiffOn
    · refine ContDiffOn.sum fun i _ ↦ (hsq (G i)).contDiffOn.mul ?_
      refine contDiffOn_prod fun k _ ↦ ?_
      exact ContDiffOn.zpow_of_ne_zero (contDiffOn_l2Norm_block k)
        (fun z hz ↦ (vectorL2Norm_pos (hz k)).ne') _
end ChartDenominatorAlt
end GroundTheory.Heights₂.Heights
