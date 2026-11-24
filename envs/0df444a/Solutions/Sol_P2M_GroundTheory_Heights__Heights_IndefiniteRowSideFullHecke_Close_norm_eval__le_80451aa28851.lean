-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_norm_eval__le_80451aa28851
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:10:38.783587+00:00
-- url     : https://prove2.me/submissions/3eca6b09-e0fb-4dd9-a7a7-78248bd439be

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_SectionInjectivityHypothesesProjectiveLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_OneBlockIdealEqComapProjIdeal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_RenameBlockIsWeightedHomogeneous
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_weight_one_fin_08916f924503

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (secM sec IsMultiHomog)
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
omit [Fintype ι] [DecidableEq ι]
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
theorem _root_.solution {r N : ℕ} (f : MvPolynomial (Fin r) ℤ) (hf : f.IsHomogeneous N)
    (w : Fin r → ℂ) :
    ‖eval₂ (Int.castRingHom ℂ) w f‖ ≤
      (∑ d ∈ f.support, ‖Int.castRingHom ℂ (f.coeff d)‖) * l2Norm w ^ N := by
  rw [eval₂_eq', Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun d hd ↦ ?_)
  rw [norm_mul, norm_prod]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  have hdeg : ∑ i, d i = N := by rw [← weight_one_fin]; exact hf (mem_support_iff.mp hd)
  calc ∏ i, ‖w i ^ d i‖ = ∏ i, ‖w i‖ ^ d i := by simp [norm_pow]
    _ ≤ ∏ i, l2Norm w ^ d i := Finset.prod_le_prod (fun _ _ ↦ by positivity)
        fun i _ ↦ pow_le_pow_left₀ (norm_nonneg _) (norm_le_l2Norm w i) _
    _ = l2Norm w ^ N := by rw [Finset.prod_pow_eq_pow_sum, hdeg]
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
