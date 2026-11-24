-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RegBallMass_chartDens_indicator_mono_6ce5d838cf83
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:00:50.172021+00:00
-- url     : https://prove2.me/submissions/62463ee5-0b22-40ba-8863-83ef50ffed1f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRegBallMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRegFixedBallMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRegLelongMono
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRegDensNonneg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetSumMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFiniteProjectionCluster
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PRegBallMass
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_FiniteProjectionCluster_fibre_finite_7d46f66826ee
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_fibre_finite_20785c71949c


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
open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff
noncomputable section
open GroundTheory.Heights₂.Heights.RegBallMass
variable {n d : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin (d + 1)) (Fin n) ℂ}
namespace GroundTheory.Heights₂.Heights.RegBallMass
theorem _root_.solution (hN : RegDensNonneg.Statement) (hA : IsFiniteProjection J A)
    (u : Fin n → ℂ) {ε : ℝ} (hε : 0 < ε) {S S' : Set (Fin n → ℂ)} (hS : S ⊆ S') (y : Fin (d + 1) → ℂ) :
    0 ≤ chartDens J A (S.indicator fun _ => 1) (vecCons (logReg u ε) fun _ => euclPot) y ∧
      chartDens J A (S.indicator fun _ => 1) (vecCons (logReg u ε) fun _ => euclPot) y ≤
        chartDens J A (S'.indicator fun _ => 1) (vecCons (logReg u ε) fun _ => euclPot) y := by
  have hfin : (fibre J A y).Finite := FiniteProjectionCluster.fibre_finite J A hA y
  have key : ∀ x ∈ fibre J A y, ∀ h : ∃ s, IsSheetAt J A x s,
      0 ≤ ReciprocityTheory.AnForm.maDens (fun k => (vecCons (logReg u ε) fun _ => euclPot :
        Fin (d + 1) → (Fin n → ℂ) → ℝ) k ∘ h.choose) y := by
    intro x hx h
    have := hN n d J A u ε x h.choose hε h.choose_spec
    rwa [hx.2] at this
  unfold chartDens sheetSum
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin, finsum_mem_eq_finite_toFinset_sum _ hfin]
  constructor
  · refine Finset.sum_nonneg fun x hx => ?_
    rw [Set.Finite.mem_toFinset] at hx
    split_ifs with h
    · exact mul_nonneg (Set.indicator_nonneg (fun _ _ => zero_le_one) _) (key x hx h)
    · exact le_rfl
  · refine Finset.sum_le_sum fun x hx => ?_
    rw [Set.Finite.mem_toFinset] at hx
    split_ifs with h
    · exact mul_le_mul_of_nonneg_right
        (Set.indicator_le_indicator_of_subset hS (fun _ => zero_le_one) x) (key x hx h)
    · exact le_rfl
end GroundTheory.Heights₂.Heights.RegBallMass
