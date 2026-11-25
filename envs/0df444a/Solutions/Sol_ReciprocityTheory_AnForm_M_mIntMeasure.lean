-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.mIntMeasure
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:59:19.043421+00:00
-- url     : https://prove2.me/submissions/5c38a117-c642-44d8-9e9e-c0b250ae07bd

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialPullbackStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_LocDens
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Partition
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Measure
import Theorems.Thm_ReciprocityTheory_AnForm_M_chart_weight_compact
import Theorems.Thm_ReciprocityTheory_AnForm_M_isFiniteMeasure_chartPartMeasure
import Theorems.Thm_ReciprocityTheory_AnForm_M_integral_chartPartMeasure
import Theorems.Thm_ReciprocityTheory_AnForm_M_existsPartition
import Theorems.Thm_ReciprocityTheory_AnForm_M_locDensCont

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.AnForm.M
open MeasureTheory FinHolAtlas Filter Topology
noncomputable section
variable {e : ℕ} {X : Type} [TopologicalSpace X] [MeasurableSpace X]
private theorem chiCont (A : FinHolAtlas e X) (P : ChartPartition A) (j : Fin A.n) :
    ContinuousOn (fun y => P.χ j ((A.chart j).symm y)) (A.chart j).target := by
  have h := ((P.smooth j) j).continuousOn
  rw [Set.preimage_univ, Set.inter_univ] at h
  exact h
private theorem integrableOn_part [CompactSpace X] [T2Space X] [BorelSpace X]
    (A : FinHolAtlas e X) (P : ChartPartition A) (Φ : Fin e → LocPot X)
    (hΦ : ∀ i, IsPotential A (Φ i)) (s : ℝ) (j : Fin A.n) (g : X → ℝ) (hg : Measurable g)
    (hgi : MIntegrable A Φ g) :
    IntegrableOn (fun y => g ((A.chart j).symm y) *
      max (s * (P.χ j ((A.chart j).symm y) * locDens A Φ j y)) 0) (A.chart j).target := by
  obtain ⟨hC, hCT, hz⟩ := chart_weight_compact A P Φ j
  have hL := hgi j _ hCT hC
  have hw : ContinuousOn (fun y => s * (P.χ j ((A.chart j).symm y) * locDens A Φ j y))
      (A.chart j).target :=
    continuousOn_const.mul ((chiCont A P j).mul (locDensCont A Φ hΦ j))
  have hcont : ContinuousOn (fun y => max (s * (P.χ j ((A.chart j).symm y) *
      locDens A Φ j y)) 0) (A.chart j).target :=
    fun y hy => (hw y hy).max continuousWithinAt_const
  have hsymm : AEMeasurable (fun y => g ((A.chart j).symm y)) (volume.restrict
      ((A.chart j) '' tsupport (P.χ j))) :=
    hg.comp_aemeasurable (((A.chart j).continuousOn_symm.mono hCT).aemeasurable hC.measurableSet)
  have hχ1 : ∀ x, P.χ j x ≤ 1 := fun x => by
    rw [← P.sum_eq_one x]
    exact Finset.single_le_sum (fun k _ => P.nonneg k x) (Finset.mem_univ j)
  have hCi : IntegrableOn (fun y => g ((A.chart j).symm y) *
      max (s * (P.χ j ((A.chart j).symm y) * locDens A Φ j y)) 0)
      ((A.chart j) '' tsupport (P.χ j)) := by
    refine (hL.norm.const_mul |s|).mono'
      (hsymm.mul ((hcont.mono hCT).aemeasurable hC.measurableSet)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => ?_)
    have h0 := P.nonneg j ((A.chart j).symm y)
    have h1 := hχ1 ((A.chart j).symm y)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul]
    have hm : |max (s * (P.χ j ((A.chart j).symm y) * locDens A Φ j y)) 0| ≤
        |s| * |locDens A Φ j y| := by
      rw [abs_of_nonneg (le_max_right _ _)]
      refine max_le ?_ (by positivity)
      calc s * (P.χ j ((A.chart j).symm y) * locDens A Φ j y)
          ≤ |s * (P.χ j ((A.chart j).symm y) * locDens A Φ j y)| := le_abs_self _
        _ = |s| * (P.χ j ((A.chart j).symm y) * |locDens A Φ j y|) := by
          rw [abs_mul, abs_mul, abs_of_nonneg h0]
        _ ≤ |s| * (1 * |locDens A Φ j y|) := by gcongr
        _ = |s| * |locDens A Φ j y| := by ring
    calc |g ((A.chart j).symm y)| * |max (s * (P.χ j ((A.chart j).symm y) * locDens A Φ j y)) 0|
        ≤ |g ((A.chart j).symm y)| * (|s| * |locDens A Φ j y|) := by gcongr
      _ = |s| * (|g ((A.chart j).symm y)| * |locDens A Φ j y|) := by ring
  refine IntegrableOn.of_forall_diff_eq_zero hCi (A.chart j).open_target.measurableSet ?_
  intro y hy
  simp [hz y hy.1 hy.2]
private theorem isFiniteMeasure_sum' {α : Type} [MeasurableSpace α] {n : ℕ} (μ : Fin n → Measure α)
    (h : ∀ j, IsFiniteMeasure (μ j)) : IsFiniteMeasure (∑ j, μ j) := by
  refine Finset.sum_induction μ (fun ν => IsFiniteMeasure ν) (fun a b ha hb => ?_) ?_
    (fun j _ => h j)
  · haveI := ha
    haveI := hb
    infer_instance
  · infer_instance
private theorem mul_max_sub_mul_max_neg_eq_mul (a b : ℝ) : b * max (1 * a) 0 - b * max (-1 * a) 0 = b * a := by
  rcases le_total 0 a with h | h
  · rw [max_eq_left (by linarith : (0 : ℝ) ≤ 1 * a), max_eq_right (by linarith : -1 * a ≤ 0)]
    ring
  · rw [max_eq_right (by linarith : 1 * a ≤ 0), max_eq_left (by linarith : (0 : ℝ) ≤ -1 * a)]
    ring
end
end ReciprocityTheory.AnForm.M
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open MeasureTheory FinHolAtlas Filter Topology
noncomputable section
variable {e : ℕ} {X : Type} [TopologicalSpace X] [MeasurableSpace X]
namespace ReciprocityTheory.AnForm.M
theorem _root_.solution : MIntMeasureStatement := by
  intro e X _ _ _ _ _ A Φ hΦ
  have hP : Nonempty (ChartPartition A) := existsPartition A
  refine ⟨∑ j, chartPartMeasure A hP.some Φ 1 j, ∑ j, chartPartMeasure A hP.some Φ (-1) j,
    isFiniteMeasure_sum' _ (fun j => isFiniteMeasure_chartPartMeasure A hP.some Φ hΦ 1 j),
    isFiniteMeasure_sum' _ (fun j => isFiniteMeasure_chartPartMeasure A hP.some Φ hΦ (-1) j), ?_⟩
  intro g hg hgi
  have h1 := fun j => integral_chartPartMeasure A hP.some Φ hΦ 1 j g hg hgi
  have h2 := fun j => integral_chartPartMeasure A hP.some Φ hΦ (-1) j g hg hgi
  refine ⟨integrable_finset_sum_measure.2 (fun j _ => (h1 j).1),
    integrable_finset_sum_measure.2 (fun j _ => (h2 j).1), ?_⟩
  rw [integral_finset_sum_measure (fun j _ => (h1 j).1),
    integral_finset_sum_measure (fun j _ => (h2 j).1), ← Finset.sum_sub_distrib]
  unfold mInt
  rw [dif_pos hP]
  unfold integralWith
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [(h1 j).2, (h2 j).2, ← integral_sub (integrableOn_part A hP.some Φ hΦ 1 j g hg hgi)
    (integrableOn_part A hP.some Φ hΦ (-1) j g hg hgi)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  dsimp only
  rw [mul_max_sub_mul_max_neg_eq_mul]
  ring
end ReciprocityTheory.AnForm.M
