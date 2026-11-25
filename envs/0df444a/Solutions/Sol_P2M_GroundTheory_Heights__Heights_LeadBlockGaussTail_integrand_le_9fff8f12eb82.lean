-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LeadBlockGaussTail_integrand_le_9fff8f12eb82
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:23:02.578189+00:00
-- url     : https://prove2.me/submissions/4b692351-990f-4868-80e8-22777e9c0593

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsLeadBlockGaussTail
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PLeadBlockGaussTail
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LeadBlockGaussTail_ballInd_zero_5a559a972822
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LeadBlockGaussTail_norm_det_sq_le_fb621fa6f07e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LeadBlockGaussTail_ball_indicator_le_6727de79cc83
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LeadBlockGaussTail_matGauss_eq_prod_1daa5cb7a9a6

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
open MeasureTheory Finset
open scoped ENNReal
noncomputable section
open GroundTheory.Heights₂.Heights.LeadBlockGaussTail
namespace GroundTheory.Heights₂.Heights.LeadBlockGaussTail
theorem _root_.solution {m k : ℕ} (hm : 0 < m) (r : ℝ) (π : Fin m → Fin (m + k) → ℂ) :
    matGauss π * (Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1).indicator 1
        (linProj π ((r : ℂ) • firstCoordVec (m + k))) *
        ENNReal.ofReal (‖(coordPlaneBlock π).det‖ ^ 2) ≤
      ENNReal.ofReal (Fintype.card (Equiv.Perm (Fin m))) * ∑ σ : Equiv.Perm (Fin m),
        ∏ i, ∏ j, entryFn r (Fin.castAdd k ⟨0, hm⟩) (Fin.castAdd k (σ i)) j (π i j) := by
  have hc0 : ((Fin.castAdd k (⟨0, hm⟩ : Fin m) : Fin (m + k)) : ℕ) = 0 := rfl
  have hrow : ∀ σ : Equiv.Perm (Fin m),
      ∏ i, ∏ j, entryFn r (Fin.castAdd k ⟨0, hm⟩) (Fin.castAdd k (σ i)) j (π i j) =
      matGauss π * ENNReal.ofReal (∏ i, ‖π i (Fin.castAdd k (σ i))‖ ^ 2) *
        ∏ i, ballInd r (π i (Fin.castAdd k ⟨0, hm⟩)) := by
    intro σ
    rw [matGauss_eq_prod, ENNReal.ofReal_prod_of_nonneg (fun i _ => by positivity)]
    simp only [entryFn, Finset.prod_mul_distrib]
    congr 1
    · congr 1
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [Finset.prod_eq_single (Fin.castAdd k (σ i)) (fun j _ hj => by simp [hj]) (by simp)]
      simp
    · refine Finset.prod_congr rfl fun i _ => ?_
      rw [Finset.prod_eq_single (Fin.castAdd k ⟨0, hm⟩) (fun j _ hj => by simp only [if_neg hj, ballInd_zero])
        (by simp)]
      simp
  simp_rw [hrow]
  calc _ ≤ matGauss π * (∏ i, ballInd r (π i (Fin.castAdd k ⟨0, hm⟩))) *
        ENNReal.ofReal ((Fintype.card (Equiv.Perm (Fin m)) : ℝ) *
          ∑ σ : Equiv.Perm (Fin m), ∏ i, ‖π i (Fin.castAdd k (σ i))‖ ^ 2) := by
        gcongr
        · exact ball_indicator_le π r _ hc0
        · exact norm_det_sq_le π
    _ = _ := by
        rw [ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_sum_of_nonneg (fun σ _ => by positivity)]
        simp only [Finset.mul_sum]
        refine Finset.sum_congr rfl fun σ _ => ?_
        ring
end GroundTheory.Heights₂.Heights.LeadBlockGaussTail
