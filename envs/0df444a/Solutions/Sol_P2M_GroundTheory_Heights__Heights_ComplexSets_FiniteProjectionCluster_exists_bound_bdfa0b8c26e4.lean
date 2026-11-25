-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ComplexSets_FiniteProjectionCluster_exists_bound_bdfa0b8c26e4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:30:18.498525+00:00
-- url     : https://prove2.me/submissions/f62fef70-11e1-49be-9a59-b7a2390023c4

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFiniteProjectionCluster
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFibreBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PNormalModelProper
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFiniteProjectionCluster
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_FiniteProjectionCluster_exists_monic_d58be7e7bc4c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_norm_lt_of_isRoot_map_eval_c7fa46924b2e


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.ComplexSets
open MvPolynomial Topology
noncomputable section
open GroundTheory.Heights₂.Heights.ComplexSets.FiniteProjectionCluster
variable {n d : ℕ}
namespace GroundTheory.Heights₂.Heights.ComplexSets.FiniteProjectionCluster
theorem _root_.solution (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    (hA : IsFiniteProjection J A) (c : Fin d → ℂ) (R : ℝ) :
    ∃ C : ℝ, ∀ x ∈ zeroSet J, dist (A.mulVec x) c ≤ R → ‖x‖ ≤ C := by
  choose P hPm hP using exists_monic J A hA
  let g : (Fin d → ℂ) → ℝ := fun y =>
    ∑ j, (1 + ∑ i ∈ Finset.range (P j).natDegree, ‖eval y ((P j).coeff i)‖)
  have hg : Continuous g :=
    continuous_finsetSum _ fun j _ => continuous_const.add
      (continuous_finsetSum _ fun i _ => (MvPolynomial.continuous_eval _).norm)
  obtain ⟨C, hC⟩ := (isCompact_closedBall c R).exists_bound_of_continuousOn hg.continuousOn
  refine ⟨C, fun x hx hd => ?_⟩
  have hy : A.mulVec x ∈ Metric.closedBall c R := hd
  have hgC : g (A.mulVec x) ≤ C := (Real.le_norm_self _).trans (hC _ hy)
  refine (pi_norm_le_iff_of_nonneg ((norm_nonneg _).trans (hC _ hy))).2 fun j => ?_
  have hj := IndefiniteRowSideFullHecke.ComplexSets.norm_lt_of_isRoot_map_eval (hPm j) (A.mulVec x) (hP j x hx)
  have hle : (1 + ∑ i ∈ Finset.range (P j).natDegree, ‖eval (A.mulVec x) ((P j).coeff i)‖) ≤
      g (A.mulVec x) :=
    Finset.single_le_sum (f := fun j => 1 + ∑ i ∈ Finset.range (P j).natDegree,
      ‖eval (A.mulVec x) ((P j).coeff i)‖)
      (fun k _ => add_nonneg zero_le_one (Finset.sum_nonneg fun _ _ => norm_nonneg _))
      (Finset.mem_univ j)
  linarith
end GroundTheory.Heights₂.Heights.ComplexSets.FiniteProjectionCluster
