-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_TubeCollarCompare_proof_7addca2ebced
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:11:05.373182+00:00
-- url     : https://prove2.me/submissions/d61cdccc-2fe9-4bc0-8af2-cd4f4e960ceb

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StTubeCollarCompare
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PTubeFormCompare
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PTubeCollarCompare
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_TubeCollarComparison_contDiffAt_logSq_comp_a77eed4f6186
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_TubeCollarComparison_abs_maDens_collar_le_25cd3edee1fd
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_fibre_finite_20785c71949c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_TubeFormComparison_exists_hessC_bound_adf0c8df653f
import Theorems.Thm_ReciprocityTheory_AnForm_Osgood_osgood


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
open MvPolynomial Matrix Filter Topology ReciprocityTheory.AnForm ComplexSets
open scoped ContDiff ComplexOrder
noncomputable section
open TubeFormComparison TubeCollarComparison
namespace GroundTheory.Heights₂.Heights
namespace TubeCollarCompare
theorem _root_.solution : TubeCollarCompare.Statement := by
  intro n d J A P R _hJ _hdim hA _hP
  set g : (Fin n → ℂ) → ℝ := fun x => logAbsSq P (A *ᵥ x) ^ 2 / 2 with hgdef
  set U : Set (Fin n → ℂ) := {x | eval (A *ᵥ x) P ≠ 0} with hUdef
  set K : Set (Fin n → ℂ) :=
    Metric.closedBall 0 R ∩ {x | Real.exp (-Real.exp 1) ≤ ‖eval (A *ᵥ x) P‖ ^ 2} with hKdef
  have hcont : Continuous fun x : Fin n → ℂ => eval (A *ᵥ x) P :=
    (MvPolynomial.continuous_eval P).comp (LinearMap.toContinuousLinearMap (Matrix.mulVecLin A)).continuous
  have hU : IsOpen U := isOpen_ne_fun hcont continuous_const
  have hK : IsCompact K :=
    (isCompact_closedBall 0 R).inter_right (isClosed_le continuous_const (hcont.norm.pow 2))
  have hKU : K ⊆ U := fun x hx h0 => by
    have h : Real.exp (-Real.exp 1) ≤ ‖eval (A *ᵥ x) P‖ ^ 2 := hx.2
    rw [h0, norm_zero] at h
    linarith [Real.exp_pos (-Real.exp 1), show (0 : ℝ) ^ 2 = 0 by norm_num]
  have hgU : ContDiffOn ℝ 2 g U := fun x hx => (contDiffAt_logSq_comp A P x hx).contDiffWithinAt
  obtain ⟨c, hc, hb⟩ := exists_hessC_bound (fun _ : Fin 1 => g) K hK (fun _ => U) (fun _ => hU)
    (fun _ => hKU) (fun _ => hgU)
  have hC : 0 ≤ (3 : ℝ) ^ (d + 1) * c := by positivity
  refine ⟨3 ^ (d + 1) * c, fun y => ?_⟩
  by_cases hy : y ∈ {y | -Real.exp 1 ≤ logAbsSq P y}
  swap
  · rw [Set.indicator_of_notMem hy]
    exact mul_nonneg hC (finsum_nonneg fun _ => finsum_nonneg fun _ => by split_ifs <;> positivity)
  rw [Set.indicator_of_mem hy]
  unfold tubeDens chartAbsDens sheetSum
  rw [finsum_mem_eq_finite_toFinset_sum _ (IndefiniteRowSideFullHecke.ComplexSets.fibre_finite hA y),
    finsum_mem_eq_finite_toFinset_sum _ (IndefiniteRowSideFullHecke.ComplexSets.fibre_finite hA y), Finset.mul_sum]
  refine Finset.sum_le_sum fun x hx => ?_
  rw [Set.Finite.mem_toFinset] at hx
  obtain ⟨hxZ, hxy⟩ := hx
  subst hxy
  split_ifs with hsx
  swap
  · simp
  dsimp only
  obtain ⟨V, hV, hyV, hsd, hsx', hsec, -⟩ := hsx.choose_spec
  set s := hsx.choose with hsdef
  set f := (Metric.closedBall (0 : Fin n → ℂ) R).indicator fun x => tubeWeight P (A *ᵥ x) with hfdef
  by_cases hf : f x = 0
  · rw [hf, zero_mul, abs_zero]
    exact mul_nonneg hC (abs_nonneg _)
  have hxB : x ∈ Metric.closedBall (0 : Fin n → ℂ) R := by
    by_contra h
    exact hf (Set.indicator_of_notMem h _)
  have hv1 : logAbsSq P (A *ᵥ x) ≤ -1 := by
    by_contra h
    exact hf (by simp [hfdef, Set.indicator_of_mem hxB, tubeWeight, h])
  have hP : eval (A *ᵥ x) P ≠ 0 := by
    intro h0
    simp [logAbsSq, h0] at hv1
    linarith
  have hxK : x ∈ K := by
    refine ⟨hxB, ?_⟩
    have h2 : 0 < ‖eval (A *ᵥ x) P‖ ^ 2 := by positivity
    have h3 := Real.exp_le_exp.2 (show -Real.exp 1 ≤ logAbsSq P (A *ᵥ x) from hy)
    rwa [logAbsSq, Real.exp_log h2] at h3
  have hw : |f x| ≤ 1 := by
    rw [hfdef, Set.indicator_of_mem hxB]
    simp only [tubeWeight, if_pos hv1]
    rw [abs_of_nonneg (by positivity)]
    exact inv_le_one_of_one_le₀ (by nlinarith)
  have hsa : AnalyticAt ℂ s (A *ᵥ x) :=
    analyticAt_pi_iff.2 fun i =>
      ReciprocityTheory.AnForm.Osgood.osgood _ V (fun z => s z i) hV (differentiableOn_pi.1 hsd i) _ hyV
  have hg2 : ContDiffAt ℝ 2 g (s (A *ᵥ x)) := by
    rw [hsx']
    exact contDiffAt_logSq_comp A P x hP
  have hbx := hb 0 (s (A *ᵥ x)) (by rw [hsx']; exact hxK)
  have key := abs_maDens_collar_le g s (A *ᵥ x) hsa hg2 hbx
  rw [abs_mul, abs_mul, Set.indicator_of_mem hxB, abs_one, one_mul]
  calc |f x| * |maDens (fun k => vecCons g (fun _ => euclPot) k ∘ s) (A *ᵥ x)|
      ≤ 1 * (3 ^ (d + 1) * c * maDens (fun _ : Fin (d + 1) => euclPot ∘ s) (A *ᵥ x)) :=
        mul_le_mul hw key (abs_nonneg _) zero_le_one
    _ ≤ 3 ^ (d + 1) * c * |maDens (fun k => (fun _ : Fin (d + 1) => euclPot) k ∘ s) (A *ᵥ x)| := by
        rw [one_mul]
        exact mul_le_mul_of_nonneg_left (le_abs_self _) hC
end TubeCollarCompare
end GroundTheory.Heights₂.Heights
