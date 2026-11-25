-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_AnalyticLimit_tvInt_lincomb_le_5b348dfe4313
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:59:41.478186+00:00
-- url     : https://prove2.me/submissions/295c0295-e2fc-4f4c-bb57-d86db553271f

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_HessCIsHermitian
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ProjectiveLinePartitionContinuousCoe
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_AnalyticLimit_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_AnalyticLimit_EnergySum
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_AnalyticLimit_abs_locDens_lincomb_le_7cc29db62577
import Theorems.Thm_ReciprocityTheory_AnForm_M_ima_apply
import Theorems.Thm_ReciprocityTheory_AnForm_M_rea_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.AnForm.M.ima_apply
attribute [local simp] ReciprocityTheory.AnForm.M.rea_apply



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.AnalyticLimit
open MeasureTheory
open scoped ContDiff ComplexOrder
open ReciprocityTheory.AnForm (hessC maDens mdisc levi)
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential mInt ChartPartition locDens integralWith)
noncomputable section
variable {D : ℕ}
variable {X : Type*} [TopologicalSpace X]
namespace GroundTheory.Heights₂.Heights.AnalyticLimit
theorem _root_.solution (A : FinHolAtlas D X) (Yo : Set X) {m : ℕ} (P : Fin m → LocPot X)
    (a : Fin D → Fin m → ℝ) (hpot : ∀ i, IsPotential A (P i)) (hnn : ∀ i, FormNonneg A Yo (P i))
    (hint : ∀ (σ : Fin D → Fin m) (Q : ChartPartition A) (j : Fin A.n), IntegrableOn (fun y =>
      Q.χ j ((A.chart j).symm y) * Yo.indicator 1 ((A.chart j).symm y) *
        locDens A (fun k => P (σ k)) j y) (A.chart j).target) :
    tvInt A (fun k => lincomb m (a k) P) (Yo.indicator 1) ≤
      ∑ σ : Fin D → Fin m, (∏ k, |a k (σ k)|) * mInt A (fun k => P (σ k)) (Yo.indicator 1) := by
  unfold tvInt mInt
  split_ifs with h
  · simp only [integralWith]
    calc ∑ j, ∫ y in (A.chart j).target, h.some.χ j ((A.chart j).symm y) *
            Yo.indicator 1 ((A.chart j).symm y) * |locDens A (fun k => lincomb m (a k) P) j y|
        ≤ ∑ j, ∫ y in (A.chart j).target, ∑ σ : Fin D → Fin m, (∏ k, |a k (σ k)|) *
            (h.some.χ j ((A.chart j).symm y) * Yo.indicator 1 ((A.chart j).symm y) *
              locDens A (fun k => P (σ k)) j y) := by
          refine Finset.sum_le_sum fun j _ => integral_mono_of_nonneg ?_
            (integrable_finsetSum _ fun σ _ => (hint σ h.some j).const_mul _) ?_
          · exact Filter.Eventually.of_forall fun y => mul_nonneg (mul_nonneg (h.some.nonneg j _)
              (Set.indicator_nonneg (fun _ _ => zero_le_one) _)) (abs_nonneg _)
          · refine (ae_restrict_iff' (A.chart j).open_target.measurableSet).2
              (Filter.Eventually.of_forall fun y hy => ?_)
            by_cases hY : (A.chart j).symm y ∈ Yo
            · simp only [Set.indicator_of_mem hY, Pi.one_apply, mul_one]
              calc h.some.χ j ((A.chart j).symm y) * |locDens A (fun k => lincomb m (a k) P) j y|
                  ≤ h.some.χ j ((A.chart j).symm y) * ∑ σ : Fin D → Fin m,
                      (∏ k, |a k (σ k)|) * locDens A (fun k => P (σ k)) j y :=
                    mul_le_mul_of_nonneg_left
                      (abs_locDens_lincomb_le A Yo P a hpot hnn j y hy hY) (h.some.nonneg j _)
                _ = _ := by
                    rw [Finset.mul_sum]
                    exact Finset.sum_congr rfl fun σ _ => by ring
            · simp [hY]
      _ = ∑ j, ∑ σ : Fin D → Fin m, (∏ k, |a k (σ k)|) * ∫ y in (A.chart j).target,
            h.some.χ j ((A.chart j).symm y) * Yo.indicator 1 ((A.chart j).symm y) *
              locDens A (fun k => P (σ k)) j y := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [integral_finsetSum _ fun σ _ => (hint σ h.some j).const_mul _]
          exact Finset.sum_congr rfl fun σ _ => integral_const_mul _ _
      _ = _ := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun σ _ => (Finset.mul_sum _ _ _).symm
  · simp
end GroundTheory.Heights₂.Heights.AnalyticLimit
