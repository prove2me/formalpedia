-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LatticeLemmas_HadamardMean_intersectionNumber_baseChange_c763fd917cd9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:07:22.144247+00:00
-- url     : https://prove2.me/submissions/00847853-a06a-4a7c-9e06-8f8066700e60

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Extension
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PHadamardMean
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeLemmas_re_det_gram_le_prod_0569ab2071d7

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LatticeLemmas
open NumberField Matrix GroundTheory.Heights₂.Heights
noncomputable section
namespace GroundTheory.Heights₂.Heights.LatticeLemmas
namespace HadamardMean
theorem _root_.solution : HadamardMean.Statement := by
  intro K _ _ M ι _ x hx hcard
  classical
  have hn : (0 : ℝ) < Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
  rw [HermitianBundle.deg, HermitianBundle.arithDegree, arithDegree_eq M.metric hx hcard, degreeWith]
  refine (div_le_div_iff_of_pos_right hn).mpr ?_
  have hσ : ∀ σ : K →+* ℂ,
      Real.log (gramDet M.metric σ x) ≤ 2 * ∑ i, Real.log (M.normAt σ (x i)) := by
    intro σ
    have hne : ∀ i, fibreVec M.metric σ (x i) ≠ 0 := fun i ↦
      (linearIndependent_fibreVec M.metric σ hx).ne_zero i
    have h1 : gramDet M.metric σ x ≤ ∏ i, ‖fibreVec M.metric σ (x i)‖ ^ 2 :=
      re_det_gram_le_prod _
    calc Real.log (gramDet M.metric σ x)
        ≤ Real.log (∏ i, ‖fibreVec M.metric σ (x i)‖ ^ 2) :=
          Real.log_le_log (gramDet_pos M.metric σ hx) h1
      _ = ∑ i, Real.log (‖fibreVec M.metric σ (x i)‖ ^ 2) := by
          rw [Real.log_prod]
          intro i _
          exact pow_ne_zero 2 (norm_ne_zero_iff.mpr (hne i))
      _ = 2 * ∑ i, Real.log (M.normAt σ (x i)) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          rw [Real.log_pow, HermitianBundle.normAt]
          push_cast
          rfl
  have hsum : ∑ σ : K →+* ℂ, Real.log (gramDet M.metric σ x) ≤
      2 * ∑ i, ∑ σ : K →+* ℂ, Real.log (M.normAt σ (x i)) := by
    rw [Finset.sum_comm (f := fun i σ ↦ Real.log (M.normAt σ (x i))), Finset.mul_sum]
    exact Finset.sum_le_sum fun σ _ ↦ hσ σ
  have hc := Real.log_natCast_nonneg
    (Nat.card (M.carrier ⧸ Submodule.span (𝓞 K) (Set.range x)))
  linarith
end HadamardMean
end GroundTheory.Heights₂.Heights.LatticeLemmas
